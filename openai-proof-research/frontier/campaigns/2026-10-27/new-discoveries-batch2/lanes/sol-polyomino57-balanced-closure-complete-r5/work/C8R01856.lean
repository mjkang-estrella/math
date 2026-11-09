import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01856G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1856_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c8r1856targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c8r1856choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1856targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)] c8r1856choice = true := by decide
    refine ⟨c8r1856targets, c8r1856choice, ?_, checked⟩
    intro S h
    simp only [c8r1856targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 31 _ (by rfl)
  have c8r1857_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c8r1857targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c8r1857choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1857targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)] c8r1857choice = true := by decide
    refine ⟨c8r1857targets, c8r1857choice, ?_, checked⟩
    intro S h
    simp only [c8r1857targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 2 _ (by rfl)
  have c8r1858_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c8r1858targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c8r1858choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1858targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)] c8r1858choice = true := by decide
    refine ⟨c8r1858targets, c8r1858choice, ?_, checked⟩
    intro S h
    simp only [c8r1858targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 5 _ (by rfl)
  have c8r1859_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c8r1859targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c8r1859choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1859targets [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)] c8r1859choice = true := by decide
    refine ⟨c8r1859targets, c8r1859choice, ?_, checked⟩
    intro S h
    simp only [c8r1859targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 8 _ (by rfl)
  have c8r1860_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)] := by
    let c8r1860targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1860choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1860targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)] c8r1860choice = true := by decide
    refine ⟨c8r1860targets, c8r1860choice, ?_, checked⟩
    intro S h
    simp only [c8r1860targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 13 _ (by rfl)
  have c8r1861_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)] := by
    let c8r1861targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c8r1861choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1861targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)] c8r1861choice = true := by decide
    refine ⟨c8r1861targets, c8r1861choice, ?_, checked⟩
    intro S h
    simp only [c8r1861targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 15 _ (by rfl)
  have c8r1862_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)] := by
    let c8r1862targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c8r1862choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1862targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)] c8r1862choice = true := by decide
    refine ⟨c8r1862targets, c8r1862choice, ?_, checked⟩
    intro S h
    simp only [c8r1862targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 17 _ (by rfl)
  have c8r1863_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)] := by
    let c8r1863targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)]]
    let c8r1863choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1863targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)] c8r1863choice = true := by decide
    refine ⟨c8r1863targets, c8r1863choice, ?_, checked⟩
    intro S h
    simp only [c8r1863targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1856_closed
  · subst row; exact c8r1857_closed
  · subst row; exact c8r1858_closed
  · subst row; exact c8r1859_closed
  · subst row; exact c8r1860_closed
  · subst row; exact c8r1861_closed
  · subst row; exact c8r1862_closed
  · subst row; exact c8r1863_closed
theorem C8R01856G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1864_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)] := by
    let c8r1864targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)]]
    let c8r1864choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1864targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)] c8r1864choice = true := by decide
    refine ⟨c8r1864targets, c8r1864choice, ?_, checked⟩
    intro S h
    simp only [c8r1864targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 22 _ (by rfl)
  have c8r1865_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)] := by
    let c8r1865targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c8r1865choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,4),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1865targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)] c8r1865choice = true := by decide
    refine ⟨c8r1865targets, c8r1865choice, ?_, checked⟩
    intro S h
    simp only [c8r1865targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 26 _ (by rfl)
  have c8r1866_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)] := by
    let c8r1866targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c8r1866choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1866targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)] c8r1866choice = true := by decide
    refine ⟨c8r1866targets, c8r1866choice, ?_, checked⟩
    intro S h
    simp only [c8r1866targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
  have c8r1867_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)] := by
    let c8r1867targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c8r1867choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,3),(12,(0,0))),((6,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1867targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)] c8r1867choice = true := by decide
    refine ⟨c8r1867targets, c8r1867choice, ?_, checked⟩
    intro S h
    simp only [c8r1867targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
  have c8r1868_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)] := by
    let c8r1868targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c8r1868choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1868targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)] c8r1868choice = true := by decide
    refine ⟨c8r1868targets, c8r1868choice, ?_, checked⟩
    intro S h
    simp only [c8r1868targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
  have c8r1869_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)] := by
    let c8r1869targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c8r1869choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,3),(12,(0,0))),((6,1),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1869targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)] c8r1869choice = true := by decide
    refine ⟨c8r1869targets, c8r1869choice, ?_, checked⟩
    intro S h
    simp only [c8r1869targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 5 _ (by rfl)
  have c8r1870_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)] := by
    let c8r1870targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c8r1870choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,2),(14,(0,0))),((7,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1870targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)] c8r1870choice = true := by decide
    refine ⟨c8r1870targets, c8r1870choice, ?_, checked⟩
    intro S h
    simp only [c8r1870targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 8 _ (by rfl)
  have c8r1871_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c8r1871targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c8r1871choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1871targets [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)] c8r1871choice = true := by decide
    refine ⟨c8r1871targets, c8r1871choice, ?_, checked⟩
    intro S h
    simp only [c8r1871targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1864_closed
  · subst row; exact c8r1865_closed
  · subst row; exact c8r1866_closed
  · subst row; exact c8r1867_closed
  · subst row; exact c8r1868_closed
  · subst row; exact c8r1869_closed
  · subst row; exact c8r1870_closed
  · subst row; exact c8r1871_closed
theorem C8R01856G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1872_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)] := by
    let c8r1872targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1872choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1872targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)] c8r1872choice = true := by decide
    refine ⟨c8r1872targets, c8r1872choice, ?_, checked⟩
    intro S h
    simp only [c8r1872targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
  have c8r1873_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)] := by
    let c8r1873targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]
    let c8r1873choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1873targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)] c8r1873choice = true := by decide
    refine ⟨c8r1873targets, c8r1873choice, ?_, checked⟩
    intro S h
    simp only [c8r1873targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
  have c8r1874_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)] := by
    let c8r1874targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)]]
    let c8r1874choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1874targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)] c8r1874choice = true := by decide
    refine ⟨c8r1874targets, c8r1874choice, ?_, checked⟩
    intro S h
    simp only [c8r1874targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 22 _ (by rfl)
  have c8r1875_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)] := by
    let c8r1875targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)]]
    let c8r1875choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1875targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)] c8r1875choice = true := by decide
    refine ⟨c8r1875targets, c8r1875choice, ?_, checked⟩
    intro S h
    simp only [c8r1875targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 26 _ (by rfl)
  have c8r1876_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)] := by
    let c8r1876targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c8r1876choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,4),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1876targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)] c8r1876choice = true := by decide
    refine ⟨c8r1876targets, c8r1876choice, ?_, checked⟩
    intro S h
    simp only [c8r1876targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 2 _ (by rfl)
  have c8r1877_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)] := by
    let c8r1877targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c8r1877choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1877targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)] c8r1877choice = true := by decide
    refine ⟨c8r1877targets, c8r1877choice, ?_, checked⟩
    intro S h
    simp only [c8r1877targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 5 _ (by rfl)
  have c8r1878_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)] := by
    let c8r1878targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c8r1878choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1878targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)] c8r1878choice = true := by decide
    refine ⟨c8r1878targets, c8r1878choice, ?_, checked⟩
    intro S h
    simp only [c8r1878targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 7 _ (by rfl)
  have c8r1879_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)] := by
    let c8r1879targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c8r1879choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1879targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)] c8r1879choice = true := by decide
    refine ⟨c8r1879targets, c8r1879choice, ?_, checked⟩
    intro S h
    simp only [c8r1879targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 9 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1872_closed
  · subst row; exact c8r1873_closed
  · subst row; exact c8r1874_closed
  · subst row; exact c8r1875_closed
  · subst row; exact c8r1876_closed
  · subst row; exact c8r1877_closed
  · subst row; exact c8r1878_closed
  · subst row; exact c8r1879_closed
theorem C8R01856G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1880_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)] := by
    let c8r1880targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)]]
    let c8r1880choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1880targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)] c8r1880choice = true := by decide
    refine ⟨c8r1880targets, c8r1880choice, ?_, checked⟩
    intro S h
    simp only [c8r1880targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 12 _ (by rfl)
  have c8r1881_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)] := by
    let c8r1881targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)]]
    let c8r1881choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1881targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)] c8r1881choice = true := by decide
    refine ⟨c8r1881targets, c8r1881choice, ?_, checked⟩
    intro S h
    simp only [c8r1881targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 14 _ (by rfl)
  have c8r1882_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)] := by
    let c8r1882targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)]]
    let c8r1882choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,3),(12,(0,0))),((6,1),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1882targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)] c8r1882choice = true := by decide
    refine ⟨c8r1882targets, c8r1882choice, ?_, checked⟩
    intro S h
    simp only [c8r1882targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 17 _ (by rfl)
  have c8r1883_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)] := by
    let c8r1883targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)]]
    let c8r1883choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,2),(14,(0,0))),((7,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1883targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)] c8r1883choice = true := by decide
    refine ⟨c8r1883targets, c8r1883choice, ?_, checked⟩
    intro S h
    simp only [c8r1883targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 20 _ (by rfl)
  have c8r1884_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)] := by
    let c8r1884targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c8r1884choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1884targets [(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)] c8r1884choice = true := by decide
    refine ⟨c8r1884targets, c8r1884choice, ?_, checked⟩
    intro S h
    simp only [c8r1884targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 24 _ (by rfl)
  have c8r1885_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)] := by
    let c8r1885targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)]]
    let c8r1885choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,3),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1885targets [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)] c8r1885choice = true := by decide
    refine ⟨c8r1885targets, c8r1885choice, ?_, checked⟩
    intro S h
    simp only [c8r1885targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 29 _ (by rfl)
  have c8r1886_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)] := by
    let c8r1886targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)]]
    let c8r1886choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1886targets [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)] c8r1886choice = true := by decide
    refine ⟨c8r1886targets, c8r1886choice, ?_, checked⟩
    intro S h
    simp only [c8r1886targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 31 _ (by rfl)
  have c8r1887_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)] := by
    let c8r1887targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)]]
    let c8r1887choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,2),(14,(0,0))),((7,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1887targets [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)] c8r1887choice = true := by decide
    refine ⟨c8r1887targets, c8r1887choice, ?_, checked⟩
    intro S h
    simp only [c8r1887targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,false] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1880_closed
  · subst row; exact c8r1881_closed
  · subst row; exact c8r1882_closed
  · subst row; exact c8r1883_closed
  · subst row; exact c8r1884_closed
  · subst row; exact c8r1885_closed
  · subst row; exact c8r1886_closed
  · subst row; exact c8r1887_closed
theorem C8R01856_closed (row : List GridPoint) (h : FamilyMember row F8B000L58) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L58, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01856G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01856G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01856G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01856G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01856G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01856G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01856G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01856G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01856G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01856G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01856G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01856G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01856G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01856G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01856G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01856G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01856G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01856G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01856G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01856G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01856G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01856G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01856G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01856G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01856G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01856G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01856G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01856G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01856G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01856G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01856G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01856G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
