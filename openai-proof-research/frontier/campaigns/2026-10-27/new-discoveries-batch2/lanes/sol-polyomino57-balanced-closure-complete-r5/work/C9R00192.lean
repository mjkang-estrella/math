import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R00192G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r192_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4)] := by
    let c9r192targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4),(3,4)]]
    let c9r192choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r192targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4)] c9r192choice = true := by decide
    refine ⟨c9r192targets, c9r192choice, ?_, checked⟩
    intro S h
    simp only [c9r192targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 10 _ (by rfl)
  have c9r193_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,3)] := by
    let c9r193targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,3),(4,3)]]
    let c9r193choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,4),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r193targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3),(3,3)] c9r193choice = true := by decide
    refine ⟨c9r193targets, c9r193choice, ?_, checked⟩
    intro S h
    simp only [c9r193targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 13 _ (by rfl)
  have c9r194_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6)] := by
    let c9r194targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6),(2,6)]]
    let c9r194choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,7),(11,(0,0))),((2,1),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r194targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6)] c9r194choice = true := by decide
    refine ⟨c9r194targets, c9r194choice, ?_, checked⟩
    intro S h
    simp only [c9r194targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 18 _ (by rfl)
  have c9r195_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1)] := by
    let c9r195targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1),(3,1)]]
    let c9r195choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,6),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((3,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r195targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1)] c9r195choice = true := by decide
    refine ⟨c9r195targets, c9r195choice, ?_, checked⟩
    intro S h
    simp only [c9r195targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 23 _ (by rfl)
  have c9r196_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4)] := by
    let c9r196targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4),(3,4)]]
    let c9r196choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,6),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r196targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4)] c9r196choice = true := by decide
    refine ⟨c9r196targets, c9r196choice, ?_, checked⟩
    intro S h
    simp only [c9r196targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 26 _ (by rfl)
  have c9r197_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,5)] := by
    let c9r197targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,5),(3,5)]]
    let c9r197choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,6),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((2,6),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r197targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,5)] c9r197choice = true := by decide
    refine ⟨c9r197targets, c9r197choice, ?_, checked⟩
    intro S h
    simp only [c9r197targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 28 _ (by rfl)
  have c9r198_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)] := by
    let c9r198targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,1)]]
    let c9r198choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,-1),(11,(0,1))),((2,2),(12,(0,0))),((2,4),(13,(0,0))),((3,0),(14,(0,0))),((3,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r198targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)] c9r198choice = true := by decide
    refine ⟨c9r198targets, c9r198choice, ?_, checked⟩
    intro S h
    simp only [c9r198targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 0 _ (by rfl)
  have c9r199_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2)] := by
    let c9r199targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2),(3,2)]]
    let c9r199choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((3,1),(14,(0,0))),((3,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r199targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2)] c9r199choice = true := by decide
    refine ⟨c9r199targets, c9r199choice, ?_, checked⟩
    intro S h
    simp only [c9r199targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r192_closed
  · subst row; exact c9r193_closed
  · subst row; exact c9r194_closed
  · subst row; exact c9r195_closed
  · subst row; exact c9r196_closed
  · subst row; exact c9r197_closed
  · subst row; exact c9r198_closed
  · subst row; exact c9r199_closed
theorem C9R00192G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r200_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4)] := by
    let c9r200targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4),(3,4)]]
    let c9r200choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0))),((2,5),(14,(0,0))),((3,1),(15,(0,0))),((3,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r200targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4)] c9r200choice = true := by decide
    refine ⟨c9r200targets, c9r200choice, ?_, checked⟩
    intro S h
    simp only [c9r200targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 8 _ (by rfl)
  have c9r201_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1)] := by
    let c9r201targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1),(4,1)]]
    let c9r201choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0))),((3,0),(14,(0,0))),((3,2),(15,(0,0))),((4,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r201targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1)] c9r201choice = true := by decide
    refine ⟨c9r201targets, c9r201choice, ?_, checked⟩
    intro S h
    simp only [c9r201targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 11 _ (by rfl)
  have c9r202_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4)] := by
    let c9r202targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4),(3,4)]]
    let c9r202choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,5),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r202targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4)] c9r202choice = true := by decide
    refine ⟨c9r202targets, c9r202choice, ?_, checked⟩
    intro S h
    simp only [c9r202targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 15 _ (by rfl)
  have c9r203_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5)] := by
    let c9r203targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5),(3,5)]]
    let c9r203choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,6),(13,(0,0))),((3,4),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r203targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5)] c9r203choice = true := by decide
    refine ⟨c9r203targets, c9r203choice, ?_, checked⟩
    intro S h
    simp only [c9r203targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 18 _ (by rfl)
  have c9r204_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4)] := by
    let c9r204targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4),(4,4)]]
    let c9r204choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,3),(14,(0,0))),((3,5),(15,(0,0))),((4,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r204targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4),(3,4)] c9r204choice = true := by decide
    refine ⟨c9r204targets, c9r204choice, ?_, checked⟩
    intro S h
    simp only [c9r204targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 21 _ (by rfl)
  have c9r205_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)] := by
    let c9r205targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,2)]]
    let c9r205choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,-1),(11,(0,1))),((2,3),(12,(0,0))),((3,0),(13,(0,0))),((3,1),(14,(0,0))),((3,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r205targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)] c9r205choice = true := by decide
    refine ⟨c9r205targets, c9r205choice, ?_, checked⟩
    intro S h
    simp only [c9r205targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 25 _ (by rfl)
  have c9r206_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)] := by
    let c9r206targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(4,0)]]
    let c9r206choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,-1),(11,(0,1))),((2,2),(12,(0,0))),((3,-1),(13,(0,1))),((3,1),(14,(0,0))),((4,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r206targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)] c9r206choice = true := by decide
    refine ⟨c9r206targets, c9r206choice, ?_, checked⟩
    intro S h
    simp only [c9r206targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 27 _ (by rfl)
  have c9r207_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)] := by
    let c9r207targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,1)]]
    let c9r207choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,-1),(11,(0,1))),((2,2),(12,(0,0))),((3,0),(13,(0,0))),((3,2),(14,(0,0))),((4,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r207targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)] c9r207choice = true := by decide
    refine ⟨c9r207targets, c9r207choice, ?_, checked⟩
    intro S h
    simp only [c9r207targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r200_closed
  · subst row; exact c9r201_closed
  · subst row; exact c9r202_closed
  · subst row; exact c9r203_closed
  · subst row; exact c9r204_closed
  · subst row; exact c9r205_closed
  · subst row; exact c9r206_closed
  · subst row; exact c9r207_closed
theorem C9R00192G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r208_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3)] := by
    let c9r208targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,3)]]
    let c9r208choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0))),((3,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r208targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3)] c9r208choice = true := by decide
    refine ⟨c9r208targets, c9r208choice, ?_, checked⟩
    intro S h
    simp only [c9r208targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 1 _ (by rfl)
  have c9r209_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1)] := by
    let c9r209targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1),(4,1)]]
    let c9r209choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((3,0),(13,(0,0))),((3,2),(14,(0,0))),((4,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r209targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1)] c9r209choice = true := by decide
    refine ⟨c9r209targets, c9r209choice, ?_, checked⟩
    intro S h
    simp only [c9r209targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 4 _ (by rfl)
  have c9r210_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2)] := by
    let c9r210targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2),(4,2)]]
    let c9r210choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((3,1),(13,(0,0))),((3,3),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r210targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,2)] c9r210choice = true := by decide
    refine ⟨c9r210targets, c9r210choice, ?_, checked⟩
    intro S h
    simp only [c9r210targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 6 _ (by rfl)
  have c9r211_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)] := by
    let c9r211targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,1)]]
    let c9r211choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((3,-1),(13,(0,1))),((3,2),(14,(0,0))),((4,0),(15,(0,0))),((4,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r211targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)] c9r211choice = true := by decide
    refine ⟨c9r211targets, c9r211choice, ?_, checked⟩
    intro S h
    simp only [c9r211targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 9 _ (by rfl)
  have c9r212_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2)] := by
    let c9r212targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2),(4,2)]]
    let c9r212choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((3,0),(13,(0,0))),((3,3),(14,(0,0))),((4,1),(15,(0,0))),((4,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r212targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2)] c9r212choice = true := by decide
    refine ⟨c9r212targets, c9r212choice, ?_, checked⟩
    intro S h
    simp only [c9r212targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 12 _ (by rfl)
  have c9r213_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1)] := by
    let c9r213targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(5,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(5,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1),(5,1)]]
    let c9r213choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((3,0),(13,(0,0))),((3,2),(14,(0,0))),((4,0),(15,(0,0))),((4,2),(16,(0,0))),((5,1),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r213targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1)] c9r213choice = true := by decide
    refine ⟨c9r213targets, c9r213choice, ?_, checked⟩
    intro S h
    simp only [c9r213targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 15 _ (by rfl)
  have c9r214_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5)] := by
    let c9r214targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c9r214choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,6),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r214targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5)] c9r214choice = true := by decide
    refine ⟨c9r214targets, c9r214choice, ?_, checked⟩
    intro S h
    simp only [c9r214targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 20 _ (by rfl)
  have c9r215_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2)] := by
    let c9r215targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c9r215choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,5),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r215targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2)] c9r215choice = true := by decide
    refine ⟨c9r215targets, c9r215choice, ?_, checked⟩
    intro S h
    simp only [c9r215targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r208_closed
  · subst row; exact c9r209_closed
  · subst row; exact c9r210_closed
  · subst row; exact c9r211_closed
  · subst row; exact c9r212_closed
  · subst row; exact c9r213_closed
  · subst row; exact c9r214_closed
  · subst row; exact c9r215_closed
theorem C9R00192G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r216_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3)] := by
    let c9r216targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c9r216choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,5),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r216targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3)] c9r216choice = true := by decide
    refine ⟨c9r216targets, c9r216choice, ?_, checked⟩
    intro S h
    simp only [c9r216targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 26 _ (by rfl)
  have c9r217_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4)] := by
    let c9r217targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c9r217choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,5),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r217targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4)] c9r217choice = true := by decide
    refine ⟨c9r217targets, c9r217choice, ?_, checked⟩
    intro S h
    simp only [c9r217targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 28 _ (by rfl)
  have c9r218_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2)] := by
    let c9r218targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,2)]]
    let c9r218choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,3),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r218targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2)] c9r218choice = true := by decide
    refine ⟨c9r218targets, c9r218choice, ?_, checked⟩
    intro S h
    simp only [c9r218targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 0 _ (by rfl)
  have c9r219_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3)] := by
    let c9r219targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,3)]]
    let c9r219choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r219targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3)] c9r219choice = true := by decide
    refine ⟨c9r219targets, c9r219choice, ?_, checked⟩
    intro S h
    simp only [c9r219targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 3 _ (by rfl)
  have c9r220_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2)] := by
    let c9r220targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,2)]]
    let c9r220choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r220targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2)] c9r220choice = true := by decide
    refine ⟨c9r220targets, c9r220choice, ?_, checked⟩
    intro S h
    simp only [c9r220targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 6 _ (by rfl)
  have c9r221_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4)] := by
    let c9r221targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4),(3,4)]]
    let c9r221choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r221targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4)] c9r221choice = true := by decide
    refine ⟨c9r221targets, c9r221choice, ?_, checked⟩
    intro S h
    simp only [c9r221targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 9 _ (by rfl)
  have c9r222_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3)] := by
    let c9r222targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3),(4,3)]]
    let c9r222choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r222targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3),(3,3)] c9r222choice = true := by decide
    refine ⟨c9r222targets, c9r222choice, ?_, checked⟩
    intro S h
    simp only [c9r222targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 12 _ (by rfl)
  have c9r223_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6)] := by
    let c9r223targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,6)]]
    let c9r223choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,7),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r223targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6)] c9r223choice = true := by decide
    refine ⟨c9r223targets, c9r223choice, ?_, checked⟩
    intro S h
    simp only [c9r223targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r216_closed
  · subst row; exact c9r217_closed
  · subst row; exact c9r218_closed
  · subst row; exact c9r219_closed
  · subst row; exact c9r220_closed
  · subst row; exact c9r221_closed
  · subst row; exact c9r222_closed
  · subst row; exact c9r223_closed
theorem C9R00192_closed (row : List GridPoint) (h : FamilyMember row F9B000L6) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L6, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R00192G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00192G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00192G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00192G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00192G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00192G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00192G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00192G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00192G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00192G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00192G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00192G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00192G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00192G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00192G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00192G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00192G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00192G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00192G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00192G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00192G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00192G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00192G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00192G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00192G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00192G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00192G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00192G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00192G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00192G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00192G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00192G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
