import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R01920G0 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1920_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)] := by
    let c8r1920targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
    let c8r1920choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1920targets [(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)] c8r1920choice = true := by decide
    refine ⟨c8r1920targets, c8r1920choice, ?_, checked⟩
    intro S h
    simp only [c8r1920targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 13 _ (by rfl)
  have c8r1921_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)] := by
    let c8r1921targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
    let c8r1921choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1921targets [(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)] c8r1921choice = true := by decide
    refine ⟨c8r1921targets, c8r1921choice, ?_, checked⟩
    intro S h
    simp only [c8r1921targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 17 _ (by rfl)
  have c8r1922_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c8r1922targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1922choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1922targets [(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)] c8r1922choice = true := by decide
    refine ⟨c8r1922targets, c8r1922choice, ?_, checked⟩
    intro S h
    simp only [c8r1922targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 25 _ (by rfl)
  have c8r1923_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)] := by
    let c8r1923targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1923choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,5),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1923targets [(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)] c8r1923choice = true := by decide
    refine ⟨c8r1923targets, c8r1923choice, ?_, checked⟩
    intro S h
    simp only [c8r1923targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 1 _ (by rfl)
  have c8r1924_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1924targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1924choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1924targets [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)] c8r1924choice = true := by decide
    refine ⟨c8r1924targets, c8r1924choice, ?_, checked⟩
    intro S h
    simp only [c8r1924targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 8 _ (by rfl)
  have c8r1925_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r1925targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r1925choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1925targets [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0)] c8r1925choice = true := by decide
    refine ⟨c8r1925targets, c8r1925choice, ?_, checked⟩
    intro S h
    simp only [c8r1925targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 11 _ (by rfl)
  have c8r1926_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r1926targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1926choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1926targets [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)] c8r1926choice = true := by decide
    refine ⟨c8r1926targets, c8r1926choice, ?_, checked⟩
    intro S h
    simp only [c8r1926targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 13 _ (by rfl)
  have c8r1927_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r1927targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1927choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1927targets [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)] c8r1927choice = true := by decide
    refine ⟨c8r1927targets, c8r1927choice, ?_, checked⟩
    intro S h
    simp only [c8r1927targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1920_closed
  · subst row; exact c8r1921_closed
  · subst row; exact c8r1922_closed
  · subst row; exact c8r1923_closed
  · subst row; exact c8r1924_closed
  · subst row; exact c8r1925_closed
  · subst row; exact c8r1926_closed
  · subst row; exact c8r1927_closed
theorem C8R01920G1 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1928_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r1928targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r1928choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1928targets [(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1)] c8r1928choice = true := by decide
    refine ⟨c8r1928targets, c8r1928choice, ?_, checked⟩
    intro S h
    simp only [c8r1928targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 20 _ (by rfl)
  have c8r1929_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r1929targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r1929choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,3),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1929targets [(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2)] c8r1929choice = true := by decide
    refine ⟨c8r1929targets, c8r1929choice, ?_, checked⟩
    intro S h
    simp only [c8r1929targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 26 _ (by rfl)
  have c8r1930_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1930targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1930choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1930targets [(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r1930choice = true := by decide
    refine ⟨c8r1930targets, c8r1930choice, ?_, checked⟩
    intro S h
    simp only [c8r1930targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 2 _ (by rfl)
  have c8r1931_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r1931targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r1931choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,6),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1931targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r1931choice = true := by decide
    refine ⟨c8r1931targets, c8r1931choice, ?_, checked⟩
    intro S h
    simp only [c8r1931targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 14 _ (by rfl)
  have c8r1932_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c8r1932targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c8r1932choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1932targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c8r1932choice = true := by decide
    refine ⟨c8r1932targets, c8r1932choice, ?_, checked⟩
    intro S h
    simp only [c8r1932targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 19 _ (by rfl)
  have c8r1933_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r1933targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r1933choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1933targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r1933choice = true := by decide
    refine ⟨c8r1933targets, c8r1933choice, ?_, checked⟩
    intro S h
    simp only [c8r1933targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 23 _ (by rfl)
  have c8r1934_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r1934targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r1934choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1934targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r1934choice = true := by decide
    refine ⟨c8r1934targets, c8r1934choice, ?_, checked⟩
    intro S h
    simp only [c8r1934targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 26 _ (by rfl)
  have c8r1935_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r1935targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r1935choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1935targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r1935choice = true := by decide
    refine ⟨c8r1935targets, c8r1935choice, ?_, checked⟩
    intro S h
    simp only [c8r1935targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1928_closed
  · subst row; exact c8r1929_closed
  · subst row; exact c8r1930_closed
  · subst row; exact c8r1931_closed
  · subst row; exact c8r1932_closed
  · subst row; exact c8r1933_closed
  · subst row; exact c8r1934_closed
  · subst row; exact c8r1935_closed
theorem C8R01920G2 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1936_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r1936targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r1936choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1936targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r1936choice = true := by decide
    refine ⟨c8r1936targets, c8r1936choice, ?_, checked⟩
    intro S h
    simp only [c8r1936targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 30 _ (by rfl)
  have c8r1937_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r1937targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r1937choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1937targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)] c8r1937choice = true := by decide
    refine ⟨c8r1937targets, c8r1937choice, ?_, checked⟩
    intro S h
    simp only [c8r1937targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 2 _ (by rfl)
  have c8r1938_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] := by
    let c8r1938targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
    let c8r1938choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1938targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)] c8r1938choice = true := by decide
    refine ⟨c8r1938targets, c8r1938choice, ?_, checked⟩
    intro S h
    simp only [c8r1938targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 5 _ (by rfl)
  have c8r1939_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] := by
    let c8r1939targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
    let c8r1939choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1939targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)] c8r1939choice = true := by decide
    refine ⟨c8r1939targets, c8r1939choice, ?_, checked⟩
    intro S h
    simp only [c8r1939targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 8 _ (by rfl)
  have c8r1940_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] := by
    let c8r1940targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
    let c8r1940choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1940targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] c8r1940choice = true := by decide
    refine ⟨c8r1940targets, c8r1940choice, ?_, checked⟩
    intro S h
    simp only [c8r1940targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 10 _ (by rfl)
  have c8r1941_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] := by
    let c8r1941targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c8r1941choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1941targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)] c8r1941choice = true := by decide
    refine ⟨c8r1941targets, c8r1941choice, ?_, checked⟩
    intro S h
    simp only [c8r1941targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 13 _ (by rfl)
  have c8r1942_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] := by
    let c8r1942targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
    let c8r1942choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1942targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)] c8r1942choice = true := by decide
    refine ⟨c8r1942targets, c8r1942choice, ?_, checked⟩
    intro S h
    simp only [c8r1942targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 16 _ (by rfl)
  have c8r1943_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] := by
    let c8r1943targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
    let c8r1943choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1943targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)] c8r1943choice = true := by decide
    refine ⟨c8r1943targets, c8r1943choice, ?_, checked⟩
    intro S h
    simp only [c8r1943targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1936_closed
  · subst row; exact c8r1937_closed
  · subst row; exact c8r1938_closed
  · subst row; exact c8r1939_closed
  · subst row; exact c8r1940_closed
  · subst row; exact c8r1941_closed
  · subst row; exact c8r1942_closed
  · subst row; exact c8r1943_closed
theorem C8R01920G3 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1944_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] := by
    let c8r1944targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c8r1944choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1944targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)] c8r1944choice = true := by decide
    refine ⟨c8r1944targets, c8r1944choice, ?_, checked⟩
    intro S h
    simp only [c8r1944targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 22 _ (by rfl)
  have c8r1945_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] := by
    let c8r1945targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c8r1945choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1945targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)] c8r1945choice = true := by decide
    refine ⟨c8r1945targets, c8r1945choice, ?_, checked⟩
    intro S h
    simp only [c8r1945targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 25 _ (by rfl)
  have c8r1946_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] := by
    let c8r1946targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c8r1946choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1946targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)] c8r1946choice = true := by decide
    refine ⟨c8r1946targets, c8r1946choice, ?_, checked⟩
    intro S h
    simp only [c8r1946targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 28 _ (by rfl)
  have c8r1947_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] := by
    let c8r1947targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c8r1947choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1947targets [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)] c8r1947choice = true := by decide
    refine ⟨c8r1947targets, c8r1947choice, ?_, checked⟩
    intro S h
    simp only [c8r1947targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 31 _ (by rfl)
  have c8r1948_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)] := by
    let c8r1948targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1948choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1948targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)] c8r1948choice = true := by decide
    refine ⟨c8r1948targets, c8r1948choice, ?_, checked⟩
    intro S h
    simp only [c8r1948targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 4 _ (by rfl)
  have c8r1949_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)] := by
    let c8r1949targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
    let c8r1949choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1949targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)] c8r1949choice = true := by decide
    refine ⟨c8r1949targets, c8r1949choice, ?_, checked⟩
    intro S h
    simp only [c8r1949targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 6 _ (by rfl)
  have c8r1950_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] := by
    let c8r1950targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
    let c8r1950choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1950targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] c8r1950choice = true := by decide
    refine ⟨c8r1950targets, c8r1950choice, ?_, checked⟩
    intro S h
    simp only [c8r1950targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 8 _ (by rfl)
  have c8r1951_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] := by
    let c8r1951targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)]]
    let c8r1951choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1951targets [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] c8r1951choice = true := by decide
    refine ⟨c8r1951targets, c8r1951choice, ?_, checked⟩
    intro S h
    simp only [c8r1951targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,false,false] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1944_closed
  · subst row; exact c8r1945_closed
  · subst row; exact c8r1946_closed
  · subst row; exact c8r1947_closed
  · subst row; exact c8r1948_closed
  · subst row; exact c8r1949_closed
  · subst row; exact c8r1950_closed
  · subst row; exact c8r1951_closed
theorem C8R01920_closed (row : List GridPoint) (h : FamilyMember row F8B000L60) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L60, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R01920G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01920G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01920G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01920G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01920G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01920G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01920G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01920G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01920G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01920G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01920G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01920G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01920G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01920G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01920G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01920G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01920G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01920G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01920G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01920G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01920G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01920G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01920G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01920G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R01920G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R01920G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R01920G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R01920G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R01920G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R01920G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R01920G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R01920G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
