import F9All
import F8B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R02464G0 (row : List GridPoint) (h : row ∈ [[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2464_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r2464targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r2464choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2464targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r2464choice = true := by decide
    refine ⟨c8r2464targets, c8r2464choice, ?_, checked⟩
    intro S h
    simp only [c8r2464targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 9 _ (by rfl)
  have c8r2465_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] := by
    let c8r2465targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]
    let c8r2465choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2465targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] c8r2465choice = true := by decide
    refine ⟨c8r2465targets, c8r2465choice, ?_, checked⟩
    intro S h
    simp only [c8r2465targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 13 _ (by rfl)
  have c8r2466_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] := by
    let c8r2466targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)]]
    let c8r2466choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2466targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] c8r2466choice = true := by decide
    refine ⟨c8r2466targets, c8r2466choice, ?_, checked⟩
    intro S h
    simp only [c8r2466targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 15 _ (by rfl)
  have c8r2467_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] := by
    let c8r2467targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)]]
    let c8r2467choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2467targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] c8r2467choice = true := by decide
    refine ⟨c8r2467targets, c8r2467choice, ?_, checked⟩
    intro S h
    simp only [c8r2467targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 17 _ (by rfl)
  have c8r2468_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)] := by
    let c8r2468targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)]]
    let c8r2468choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2468targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)] c8r2468choice = true := by decide
    refine ⟨c8r2468targets, c8r2468choice, ?_, checked⟩
    intro S h
    simp only [c8r2468targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 21 _ (by rfl)
  have c8r2469_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)] := by
    let c8r2469targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)]]
    let c8r2469choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2469targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)] c8r2469choice = true := by decide
    refine ⟨c8r2469targets, c8r2469choice, ?_, checked⟩
    intro S h
    simp only [c8r2469targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 24 _ (by rfl)
  have c8r2470_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)] := by
    let c8r2470targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)]]
    let c8r2470choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2470targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)] c8r2470choice = true := by decide
    refine ⟨c8r2470targets, c8r2470choice, ?_, checked⟩
    intro S h
    simp only [c8r2470targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 27 _ (by rfl)
  have c8r2471_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)] := by
    let c8r2471targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)]]
    let c8r2471choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2471targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)] c8r2471choice = true := by decide
    refine ⟨c8r2471targets, c8r2471choice, ?_, checked⟩
    intro S h
    simp only [c8r2471targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2464_closed
  · subst row; exact c8r2465_closed
  · subst row; exact c8r2466_closed
  · subst row; exact c8r2467_closed
  · subst row; exact c8r2468_closed
  · subst row; exact c8r2469_closed
  · subst row; exact c8r2470_closed
  · subst row; exact c8r2471_closed
theorem C8R02464G1 (row : List GridPoint) (h : row ∈ [[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2472_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)] := by
    let c8r2472targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)]]
    let c8r2472choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2472targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)] c8r2472choice = true := by decide
    refine ⟨c8r2472targets, c8r2472choice, ?_, checked⟩
    intro S h
    simp only [c8r2472targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 2 _ (by rfl)
  have c8r2473_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)] := by
    let c8r2473targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(4,3)]]
    let c8r2473choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2473targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)] c8r2473choice = true := by decide
    refine ⟨c8r2473targets, c8r2473choice, ?_, checked⟩
    intro S h
    simp only [c8r2473targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 5 _ (by rfl)
  have c8r2474_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)] := by
    let c8r2474targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1)]]
    let c8r2474choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,2),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2474targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)] c8r2474choice = true := by decide
    refine ⟨c8r2474targets, c8r2474choice, ?_, checked⟩
    intro S h
    simp only [c8r2474targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 8 _ (by rfl)
  have c8r2475_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)] := by
    let c8r2475targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(4,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)]]
    let c8r2475choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,-1),(13,(0,1))),((4,1),(14,(0,0))),((5,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2475targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)] c8r2475choice = true := by decide
    refine ⟨c8r2475targets, c8r2475choice, ?_, checked⟩
    intro S h
    simp only [c8r2475targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 10 _ (by rfl)
  have c8r2476_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)] := by
    let c8r2476targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c8r2476choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2476targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)] c8r2476choice = true := by decide
    refine ⟨c8r2476targets, c8r2476choice, ?_, checked⟩
    intro S h
    simp only [c8r2476targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 14 _ (by rfl)
  have c8r2477_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)] := by
    let c8r2477targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)]]
    let c8r2477choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2477targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)] c8r2477choice = true := by decide
    refine ⟨c8r2477targets, c8r2477choice, ?_, checked⟩
    intro S h
    simp only [c8r2477targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 17 _ (by rfl)
  have c8r2478_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)] := by
    let c8r2478targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)]]
    let c8r2478choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2478targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)] c8r2478choice = true := by decide
    refine ⟨c8r2478targets, c8r2478choice, ?_, checked⟩
    intro S h
    simp only [c8r2478targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 19 _ (by rfl)
  have c8r2479_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)] := by
    let c8r2479targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)]]
    let c8r2479choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2479targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)] c8r2479choice = true := by decide
    refine ⟨c8r2479targets, c8r2479choice, ?_, checked⟩
    intro S h
    simp only [c8r2479targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2472_closed
  · subst row; exact c8r2473_closed
  · subst row; exact c8r2474_closed
  · subst row; exact c8r2475_closed
  · subst row; exact c8r2476_closed
  · subst row; exact c8r2477_closed
  · subst row; exact c8r2478_closed
  · subst row; exact c8r2479_closed
theorem C8R02464G2 (row : List GridPoint) (h : row ∈ [[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2480_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)] := by
    let c8r2480targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)]]
    let c8r2480choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2480targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)] c8r2480choice = true := by decide
    refine ⟨c8r2480targets, c8r2480choice, ?_, checked⟩
    intro S h
    simp only [c8r2480targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 27 _ (by rfl)
  have c8r2481_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)] := by
    let c8r2481targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)]]
    let c8r2481choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2481targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)] c8r2481choice = true := by decide
    refine ⟨c8r2481targets, c8r2481choice, ?_, checked⟩
    intro S h
    simp only [c8r2481targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 30 _ (by rfl)
  have c8r2482_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] := by
    let c8r2482targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)]]
    let c8r2482choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2482targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] c8r2482choice = true := by decide
    refine ⟨c8r2482targets, c8r2482choice, ?_, checked⟩
    intro S h
    simp only [c8r2482targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 1 _ (by rfl)
  have c8r2483_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)] := by
    let c8r2483targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)]]
    let c8r2483choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2483targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)] c8r2483choice = true := by decide
    refine ⟨c8r2483targets, c8r2483choice, ?_, checked⟩
    intro S h
    simp only [c8r2483targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 4 _ (by rfl)
  have c8r2484_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)] := by
    let c8r2484targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)]]
    let c8r2484choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2484targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)] c8r2484choice = true := by decide
    refine ⟨c8r2484targets, c8r2484choice, ?_, checked⟩
    intro S h
    simp only [c8r2484targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 7 _ (by rfl)
  have c8r2485_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)] := by
    let c8r2485targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)]]
    let c8r2485choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2485targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)] c8r2485choice = true := by decide
    refine ⟨c8r2485targets, c8r2485choice, ?_, checked⟩
    intro S h
    simp only [c8r2485targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 11 _ (by rfl)
  have c8r2486_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] := by
    let c8r2486targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c8r2486choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2486targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)] c8r2486choice = true := by decide
    refine ⟨c8r2486targets, c8r2486choice, ?_, checked⟩
    intro S h
    simp only [c8r2486targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 14 _ (by rfl)
  have c8r2487_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] := by
    let c8r2487targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)]]
    let c8r2487choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2487targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)] c8r2487choice = true := by decide
    refine ⟨c8r2487targets, c8r2487choice, ?_, checked⟩
    intro S h
    simp only [c8r2487targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2480_closed
  · subst row; exact c8r2481_closed
  · subst row; exact c8r2482_closed
  · subst row; exact c8r2483_closed
  · subst row; exact c8r2484_closed
  · subst row; exact c8r2485_closed
  · subst row; exact c8r2486_closed
  · subst row; exact c8r2487_closed
theorem C8R02464G3 (row : List GridPoint) (h : row ∈ [[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2488_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] := by
    let c8r2488targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)]]
    let c8r2488choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2488targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)] c8r2488choice = true := by decide
    refine ⟨c8r2488targets, c8r2488choice, ?_, checked⟩
    intro S h
    simp only [c8r2488targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 20 _ (by rfl)
  have c8r2489_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] := by
    let c8r2489targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)]]
    let c8r2489choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2489targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)] c8r2489choice = true := by decide
    refine ⟨c8r2489targets, c8r2489choice, ?_, checked⟩
    intro S h
    simp only [c8r2489targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 23 _ (by rfl)
  have c8r2490_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] := by
    let c8r2490targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)]]
    let c8r2490choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2490targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)] c8r2490choice = true := by decide
    refine ⟨c8r2490targets, c8r2490choice, ?_, checked⟩
    intro S h
    simp only [c8r2490targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 26 _ (by rfl)
  have c8r2491_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] := by
    let c8r2491targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)]]
    let c8r2491choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,6),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2491targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)] c8r2491choice = true := by decide
    refine ⟨c8r2491targets, c8r2491choice, ?_, checked⟩
    intro S h
    simp only [c8r2491targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 30 _ (by rfl)
  have c8r2492_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] := by
    let c8r2492targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)]]
    let c8r2492choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2492targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)] c8r2492choice = true := by decide
    refine ⟨c8r2492targets, c8r2492choice, ?_, checked⟩
    intro S h
    simp only [c8r2492targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 1 _ (by rfl)
  have c8r2493_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] := by
    let c8r2493targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)]]
    let c8r2493choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,5),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2493targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)] c8r2493choice = true := by decide
    refine ⟨c8r2493targets, c8r2493choice, ?_, checked⟩
    intro S h
    simp only [c8r2493targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 3 _ (by rfl)
  have c8r2494_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] := by
    let c8r2494targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)]]
    let c8r2494choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2494targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)] c8r2494choice = true := by decide
    refine ⟨c8r2494targets, c8r2494choice, ?_, checked⟩
    intro S h
    simp only [c8r2494targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 7 _ (by rfl)
  have c8r2495_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] := by
    let c8r2495targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)]]
    let c8r2495choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,5),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2495targets [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)] c8r2495choice = true := by decide
    refine ⟨c8r2495targets, c8r2495choice, ?_, checked⟩
    intro S h
    simp only [c8r2495targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,false,true,false,true] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2488_closed
  · subst row; exact c8r2489_closed
  · subst row; exact c8r2490_closed
  · subst row; exact c8r2491_closed
  · subst row; exact c8r2492_closed
  · subst row; exact c8r2493_closed
  · subst row; exact c8r2494_closed
  · subst row; exact c8r2495_closed
theorem C8R02464_closed (row : List GridPoint) (h : FamilyMember row F8B001L13) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B001L13, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R02464G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02464G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02464G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02464G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02464G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02464G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02464G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02464G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02464G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02464G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02464G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02464G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02464G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02464G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02464G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02464G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02464G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02464G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02464G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02464G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02464G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02464G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02464G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02464G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02464G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02464G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02464G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02464G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02464G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02464G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02464G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02464G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
