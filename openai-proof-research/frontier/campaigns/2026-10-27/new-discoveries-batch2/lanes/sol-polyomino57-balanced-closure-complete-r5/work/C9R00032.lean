import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R00032G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r32_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6)] := by
    let c9r32targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6),(2,6)]]
    let c9r32choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,5),(13,(0,0))),((1,7),(14,(0,0))),((2,4),(15,(0,0))),((2,6),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r32targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6)] c9r32choice = true := by decide
    refine ⟨c9r32targets, c9r32choice, ?_, checked⟩
    intro S h
    simp only [c9r32targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 9 _ (by rfl)
  have c9r33_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(2,4)] := by
    let c9r33targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(2,4),(3,4)]]
    let c9r33choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,3),(15,(0,0))),((2,5),(16,(0,0))),((3,4),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r33targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(2,4)] c9r33choice = true := by decide
    refine ⟨c9r33targets, c9r33choice, ?_, checked⟩
    intro S h
    simp only [c9r33targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 12 _ (by rfl)
  have c9r34_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6)] := by
    let c9r34targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6),(2,6)]]
    let c9r34choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,7),(14,(0,0))),((2,5),(15,(0,0))),((2,6),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r34targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6)] c9r34choice = true := by decide
    refine ⟨c9r34targets, c9r34choice, ?_, checked⟩
    intro S h
    simp only [c9r34targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 15 _ (by rfl)
  have c9r35_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(2,5)] := by
    let c9r35targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(2,5),(3,5)]]
    let c9r35choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,6),(14,(0,0))),((2,4),(15,(0,0))),((2,6),(16,(0,0))),((3,5),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r35targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(2,5)] c9r35choice = true := by decide
    refine ⟨c9r35targets, c9r35choice, ?_, checked⟩
    intro S h
    simp only [c9r35targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 18 _ (by rfl)
  have c9r36_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,7)] := by
    let c9r36targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,7),(2,7)]]
    let c9r36choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,8),(15,(0,0))),((2,6),(16,(0,0))),((2,7),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r36targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,7)] c9r36choice = true := by decide
    refine ⟨c9r36targets, c9r36choice, ?_, checked⟩
    intro S h
    simp only [c9r36targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 21 _ (by rfl)
  have c9r37_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(2,6)] := by
    let c9r37targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6),(3,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(2,6),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(2,6),(3,6)]]
    let c9r37choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,7),(15,(0,0))),((2,5),(16,(0,0))),((2,7),(17,(0,0))),((3,6),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r37targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(2,6)] c9r37choice = true := by decide
    refine ⟨c9r37targets, c9r37choice, ?_, checked⟩
    intro S h
    simp only [c9r37targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 24 _ (by rfl)
  have c9r38_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)] := by
    let c9r38targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)]]
    let c9r38choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,1),(13,(0,0))),((2,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r38targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)] c9r38choice = true := by decide
    refine ⟨c9r38targets, c9r38choice, ?_, checked⟩
    intro S h
    simp only [c9r38targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 31 _ (by rfl)
  have c9r39_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)] := by
    let c9r39targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,3)]]
    let c9r39choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,1),(13,(0,0))),((2,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r39targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)] c9r39choice = true := by decide
    refine ⟨c9r39targets, c9r39choice, ?_, checked⟩
    intro S h
    simp only [c9r39targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r32_closed
  · subst row; exact c9r33_closed
  · subst row; exact c9r34_closed
  · subst row; exact c9r35_closed
  · subst row; exact c9r36_closed
  · subst row; exact c9r37_closed
  · subst row; exact c9r38_closed
  · subst row; exact c9r39_closed
theorem C9R00032G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r40_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)] := by
    let c9r40targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4)]]
    let c9r40choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,1),(13,(0,0))),((2,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r40targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)] c9r40choice = true := by decide
    refine ⟨c9r40targets, c9r40choice, ?_, checked⟩
    intro S h
    simp only [c9r40targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 8 _ (by rfl)
  have c9r41_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)] := by
    let c9r41targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5)]]
    let c9r41choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,6),(12,(0,0))),((2,0),(13,(0,0))),((2,1),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r41targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)] c9r41choice = true := by decide
    refine ⟨c9r41targets, c9r41choice, ?_, checked⟩
    intro S h
    simp only [c9r41targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 12 _ (by rfl)
  have c9r42_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)] := by
    let c9r42targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(3,0)]]
    let c9r42choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,-1),(13,(0,1))),((2,1),(14,(0,0))),((3,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r42targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)] c9r42choice = true := by decide
    refine ⟨c9r42targets, c9r42choice, ?_, checked⟩
    intro S h
    simp only [c9r42targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 14 _ (by rfl)
  have c9r43_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)] := by
    let c9r43targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1),(3,1)]]
    let c9r43choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0))),((2,2),(14,(0,0))),((3,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r43targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)] c9r43choice = true := by decide
    refine ⟨c9r43targets, c9r43choice, ?_, checked⟩
    intro S h
    simp only [c9r43targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 16 _ (by rfl)
  have c9r44_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3)] := by
    let c9r44targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,3)]]
    let c9r44choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,2),(13,(0,0))),((2,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r44targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3)] c9r44choice = true := by decide
    refine ⟨c9r44targets, c9r44choice, ?_, checked⟩
    intro S h
    simp only [c9r44targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 21 _ (by rfl)
  have c9r45_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4)] := by
    let c9r45targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,4)]]
    let c9r45choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,2),(13,(0,0))),((2,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r45targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4)] c9r45choice = true := by decide
    refine ⟨c9r45targets, c9r45choice, ?_, checked⟩
    intro S h
    simp only [c9r45targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 25 _ (by rfl)
  have c9r46_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5)] := by
    let c9r46targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,5)]]
    let c9r46choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,6),(12,(0,0))),((2,0),(13,(0,0))),((2,2),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r46targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5)] c9r46choice = true := by decide
    refine ⟨c9r46targets, c9r46choice, ?_, checked⟩
    intro S h
    simp only [c9r46targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 29 _ (by rfl)
  have c9r47_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0)] := by
    let c9r47targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(3,0)]]
    let c9r47choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,-1),(13,(0,1))),((2,1),(14,(0,0))),((2,2),(15,(0,0))),((3,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r47targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0)] c9r47choice = true := by decide
    refine ⟨c9r47targets, c9r47choice, ?_, checked⟩
    intro S h
    simp only [c9r47targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r40_closed
  · subst row; exact c9r41_closed
  · subst row; exact c9r42_closed
  · subst row; exact c9r43_closed
  · subst row; exact c9r44_closed
  · subst row; exact c9r45_closed
  · subst row; exact c9r46_closed
  · subst row; exact c9r47_closed
theorem C9R00032G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r48_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2)] := by
    let c9r48targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2),(3,2)]]
    let c9r48choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0))),((2,1),(14,(0,0))),((2,3),(15,(0,0))),((3,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r48targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2)] c9r48choice = true := by decide
    refine ⟨c9r48targets, c9r48choice, ?_, checked⟩
    intro S h
    simp only [c9r48targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 3 _ (by rfl)
  have c9r49_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4)] := by
    let c9r49targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,4)]]
    let c9r49choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,3),(13,(0,0))),((2,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r49targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4)] c9r49choice = true := by decide
    refine ⟨c9r49targets, c9r49choice, ?_, checked⟩
    intro S h
    simp only [c9r49targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 7 _ (by rfl)
  have c9r50_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5)] := by
    let c9r50targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,5)]]
    let c9r50choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,4),(11,(0,0))),((1,6),(12,(0,0))),((2,0),(13,(0,0))),((2,3),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r50targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5)] c9r50choice = true := by decide
    refine ⟨c9r50targets, c9r50choice, ?_, checked⟩
    intro S h
    simp only [c9r50targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 11 _ (by rfl)
  have c9r51_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0)] := by
    let c9r51targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(3,0)]]
    let c9r51choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,-1),(13,(0,1))),((2,1),(14,(0,0))),((2,3),(15,(0,0))),((3,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r51targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0)] c9r51choice = true := by decide
    refine ⟨c9r51targets, c9r51choice, ?_, checked⟩
    intro S h
    simp only [c9r51targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 14 _ (by rfl)
  have c9r52_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3)] := by
    let c9r52targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3),(3,3)]]
    let c9r52choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0))),((2,2),(14,(0,0))),((2,4),(15,(0,0))),((3,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r52targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3)] c9r52choice = true := by decide
    refine ⟨c9r52targets, c9r52choice, ?_, checked⟩
    intro S h
    simp only [c9r52targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 17 _ (by rfl)
  have c9r53_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5)] := by
    let c9r53targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,5)]]
    let c9r53choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,6),(12,(0,0))),((2,0),(13,(0,0))),((2,4),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r53targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5)] c9r53choice = true := by decide
    refine ⟨c9r53targets, c9r53choice, ?_, checked⟩
    intro S h
    simp only [c9r53targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 21 _ (by rfl)
  have c9r54_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0)] := by
    let c9r54targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(3,0)]]
    let c9r54choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,5),(12,(0,0))),((2,-1),(13,(0,1))),((2,1),(14,(0,0))),((2,4),(15,(0,0))),((3,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r54targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0)] c9r54choice = true := by decide
    refine ⟨c9r54targets, c9r54choice, ?_, checked⟩
    intro S h
    simp only [c9r54targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 24 _ (by rfl)
  have c9r55_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4)] := by
    let c9r55targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4),(3,4)]]
    let c9r55choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0))),((2,3),(14,(0,0))),((2,5),(15,(0,0))),((3,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r55targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4)] c9r55choice = true := by decide
    refine ⟨c9r55targets, c9r55choice, ?_, checked⟩
    intro S h
    simp only [c9r55targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r48_closed
  · subst row; exact c9r49_closed
  · subst row; exact c9r50_closed
  · subst row; exact c9r51_closed
  · subst row; exact c9r52_closed
  · subst row; exact c9r53_closed
  · subst row; exact c9r54_closed
  · subst row; exact c9r55_closed
theorem C9R00032G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r56_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6)] := by
    let c9r56targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(1,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,6)]]
    let c9r56choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,7),(13,(0,0))),((2,0),(14,(0,0))),((2,5),(15,(0,0))),((2,6),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r56targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6)] c9r56choice = true := by decide
    refine ⟨c9r56targets, c9r56choice, ?_, checked⟩
    intro S h
    simp only [c9r56targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 31 _ (by rfl)
  have c9r57_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0)] := by
    let c9r57targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0),(3,0)]]
    let c9r57choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,6),(13,(0,0))),((2,-1),(14,(0,1))),((2,1),(15,(0,0))),((2,5),(16,(0,0))),((3,0),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r57targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0)] c9r57choice = true := by decide
    refine ⟨c9r57targets, c9r57choice, ?_, checked⟩
    intro S h
    simp only [c9r57targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 2 _ (by rfl)
  have c9r58_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,5)] := by
    let c9r58targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(2,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,5),(3,5)]]
    let c9r58choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,6),(13,(0,0))),((2,0),(14,(0,0))),((2,4),(15,(0,0))),((2,6),(16,(0,0))),((3,5),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r58targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,5)] c9r58choice = true := by decide
    refine ⟨c9r58targets, c9r58choice, ?_, checked⟩
    intro S h
    simp only [c9r58targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 5 _ (by rfl)
  have c9r59_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1)] := by
    let c9r59targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(3,1)]]
    let c9r59choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((2,-1),(14,(0,1))),((2,2),(15,(0,0))),((3,0),(16,(0,0))),((3,1),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r59targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1)] c9r59choice = true := by decide
    refine ⟨c9r59targets, c9r59choice, ?_, checked⟩
    intro S h
    simp only [c9r59targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 8 _ (by rfl)
  have c9r60_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0)] := by
    let c9r60targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(4,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0),(4,0)]]
    let c9r60choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((2,-1),(14,(0,1))),((2,1),(15,(0,0))),((3,-1),(16,(0,1))),((3,1),(17,(0,0))),((4,0),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r60targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0)] c9r60choice = true := by decide
    refine ⟨c9r60targets, c9r60choice, ?_, checked⟩
    intro S h
    simp only [c9r60targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 10 _ (by rfl)
  have c9r61_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)] := by
    let c9r61targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,3)]]
    let c9r61choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,4),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r61targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)] c9r61choice = true := by decide
    refine ⟨c9r61targets, c9r61choice, ?_, checked⟩
    intro S h
    simp only [c9r61targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 15 _ (by rfl)
  have c9r62_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4)] := by
    let c9r62targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(2,4)]]
    let c9r62choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r62targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4)] c9r62choice = true := by decide
    refine ⟨c9r62targets, c9r62choice, ?_, checked⟩
    intro S h
    simp only [c9r62targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 19 _ (by rfl)
  have c9r63_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5)] := by
    let c9r63targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5),(2,5)]]
    let c9r63choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((1,6),(11,(0,0))),((2,1),(12,(0,0))),((2,2),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r63targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5)] c9r63choice = true := by decide
    refine ⟨c9r63targets, c9r63choice, ?_, checked⟩
    intro S h
    simp only [c9r63targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,true,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r56_closed
  · subst row; exact c9r57_closed
  · subst row; exact c9r58_closed
  · subst row; exact c9r59_closed
  · subst row; exact c9r60_closed
  · subst row; exact c9r61_closed
  · subst row; exact c9r62_closed
  · subst row; exact c9r63_closed
theorem C9R00032_closed (row : List GridPoint) (h : FamilyMember row F9B000L1) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L1, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R00032G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00032G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00032G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00032G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00032G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00032G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00032G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00032G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00032G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00032G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00032G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00032G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00032G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00032G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00032G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00032G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00032G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00032G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00032G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00032G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00032G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00032G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00032G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00032G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00032G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00032G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00032G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00032G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00032G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00032G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00032G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00032G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
