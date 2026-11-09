import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R00000G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r0_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8)] := by
    let c9r0targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8)]]
    let c9r0choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,0),(11,(0,0))),((1,1),(12,(0,0))),((1,2),(13,(0,0))),((1,3),(14,(0,0))),((1,4),(15,(0,0))),((1,5),(16,(0,0))),((1,6),(17,(0,0))),((1,7),(18,(0,0))),((1,8),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r0targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8)] c9r0choice = true := by decide
    refine ⟨c9r0targets, c9r0choice, ?_, checked⟩
    intro S h
    simp only [c9r0targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 9 _ (by rfl)
  have c9r1_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0)] := by
    let c9r1targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(2,0)]]
    let c9r1choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,-1),(10,(0,1))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,6),(16,(0,0))),((1,7),(17,(0,0))),((2,0),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0)] c9r1choice = true := by decide
    refine ⟨c9r1targets, c9r1choice, ?_, checked⟩
    intro S h
    simp only [c9r1targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 17 _ (by rfl)
  have c9r2_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1)] := by
    let c9r2targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,1)]]
    let c9r2choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,1),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1)] c9r2choice = true := by decide
    refine ⟨c9r2targets, c9r2choice, ?_, checked⟩
    intro S h
    simp only [c9r2targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 24 _ (by rfl)
  have c9r3_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2)] := by
    let c9r3targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(2,2)]]
    let c9r3choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,2),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r3targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2)] c9r3choice = true := by decide
    refine ⟨c9r3targets, c9r3choice, ?_, checked⟩
    intro S h
    simp only [c9r3targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 30 _ (by rfl)
  have c9r4_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3)] := by
    let c9r4targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(2,3)]]
    let c9r4choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,3),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r4targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3)] c9r4choice = true := by decide
    refine ⟨c9r4targets, c9r4choice, ?_, checked⟩
    intro S h
    simp only [c9r4targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 3 _ (by rfl)
  have c9r5_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4)] := by
    let c9r5targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(2,4)]]
    let c9r5choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,4),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r5targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4)] c9r5choice = true := by decide
    refine ⟨c9r5targets, c9r5choice, ?_, checked⟩
    intro S h
    simp only [c9r5targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 7 _ (by rfl)
  have c9r6_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5)] := by
    let c9r6targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(2,5)]]
    let c9r6choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,5),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r6targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5)] c9r6choice = true := by decide
    refine ⟨c9r6targets, c9r6choice, ?_, checked⟩
    intro S h
    simp only [c9r6targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 10 _ (by rfl)
  have c9r7_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6)] := by
    let c9r7targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6),(2,6)]]
    let c9r7choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,7),(16,(0,0))),((2,6),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r7targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6)] c9r7choice = true := by decide
    refine ⟨c9r7targets, c9r7choice, ?_, checked⟩
    intro S h
    simp only [c9r7targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r0_closed
  · subst row; exact c9r1_closed
  · subst row; exact c9r2_closed
  · subst row; exact c9r3_closed
  · subst row; exact c9r4_closed
  · subst row; exact c9r5_closed
  · subst row; exact c9r6_closed
  · subst row; exact c9r7_closed
theorem C9R00000G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(2,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,7)] := by
    let c9r8targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,7),(2,7)]]
    let c9r8choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,6),(16,(0,0))),((1,8),(17,(0,0))),((2,7),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r8targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,7)] c9r8choice = true := by decide
    refine ⟨c9r8targets, c9r8choice, ?_, checked⟩
    intro S h
    simp only [c9r8targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 14 _ (by rfl)
  have c9r9_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)] := by
    let c9r9targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,1)]]
    let c9r9choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,0),(15,(0,0))),((2,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r9targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)] c9r9choice = true := by decide
    refine ⟨c9r9targets, c9r9choice, ?_, checked⟩
    intro S h
    simp only [c9r9targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 21 _ (by rfl)
  have c9r10_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2)] := by
    let c9r10targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,2)]]
    let c9r10choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,1),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,0),(15,(0,0))),((2,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r10targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2)] c9r10choice = true := by decide
    refine ⟨c9r10targets, c9r10choice, ?_, checked⟩
    intro S h
    simp only [c9r10targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 27 _ (by rfl)
  have c9r11_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3)] := by
    let c9r11targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,3)]]
    let c9r11choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,0),(15,(0,0))),((2,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r11targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3)] c9r11choice = true := by decide
    refine ⟨c9r11targets, c9r11choice, ?_, checked⟩
    intro S h
    simp only [c9r11targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 0 _ (by rfl)
  have c9r12_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4)] := by
    let c9r12targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,4)]]
    let c9r12choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,0),(15,(0,0))),((2,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r12targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4)] c9r12choice = true := by decide
    refine ⟨c9r12targets, c9r12choice, ?_, checked⟩
    intro S h
    simp only [c9r12targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 4 _ (by rfl)
  have c9r13_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5)] := by
    let c9r13targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(2,5)]]
    let c9r13choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,6),(14,(0,0))),((2,0),(15,(0,0))),((2,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r13targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5)] c9r13choice = true := by decide
    refine ⟨c9r13targets, c9r13choice, ?_, checked⟩
    intro S h
    simp only [c9r13targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 7 _ (by rfl)
  have c9r14_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6)] := by
    let c9r14targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6),(2,6)]]
    let c9r14choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,7),(15,(0,0))),((2,0),(16,(0,0))),((2,6),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r14targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6)] c9r14choice = true := by decide
    refine ⟨c9r14targets, c9r14choice, ?_, checked⟩
    intro S h
    simp only [c9r14targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 10 _ (by rfl)
  have c9r15_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(2,0)] := by
    let c9r15targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(2,0),(3,0)]]
    let c9r15choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((2,-1),(16,(0,1))),((2,1),(17,(0,0))),((3,0),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r15targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(2,0)] c9r15choice = true := by decide
    refine ⟨c9r15targets, c9r15choice, ?_, checked⟩
    intro S h
    simp only [c9r15targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8_closed
  · subst row; exact c9r9_closed
  · subst row; exact c9r10_closed
  · subst row; exact c9r11_closed
  · subst row; exact c9r12_closed
  · subst row; exact c9r13_closed
  · subst row; exact c9r14_closed
  · subst row; exact c9r15_closed
theorem C9R00000G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r16_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2)] := by
    let c9r16targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(2,2)]]
    let c9r16choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((1,6),(13,(0,0))),((2,1),(14,(0,0))),((2,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r16targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2)] c9r16choice = true := by decide
    refine ⟨c9r16targets, c9r16choice, ?_, checked⟩
    intro S h
    simp only [c9r16targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 18 _ (by rfl)
  have c9r17_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3)] := by
    let c9r17targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,3)]]
    let c9r17choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,2),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((1,6),(13,(0,0))),((2,1),(14,(0,0))),((2,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r17targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3)] c9r17choice = true := by decide
    refine ⟨c9r17targets, c9r17choice, ?_, checked⟩
    intro S h
    simp only [c9r17targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 23 _ (by rfl)
  have c9r18_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4)] := by
    let c9r18targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,4)]]
    let c9r18choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,5),(12,(0,0))),((1,6),(13,(0,0))),((2,1),(14,(0,0))),((2,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r18targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4)] c9r18choice = true := by decide
    refine ⟨c9r18targets, c9r18choice, ?_, checked⟩
    intro S h
    simp only [c9r18targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 27 _ (by rfl)
  have c9r19_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5)] := by
    let c9r19targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,5)]]
    let c9r19choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,6),(13,(0,0))),((2,1),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r19targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5)] c9r19choice = true := by decide
    refine ⟨c9r19targets, c9r19choice, ?_, checked⟩
    intro S h
    simp only [c9r19targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 30 _ (by rfl)
  have c9r20_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6)] := by
    let c9r20targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(2,6)]]
    let c9r20choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,7),(14,(0,0))),((2,1),(15,(0,0))),((2,6),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r20targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6)] c9r20choice = true := by decide
    refine ⟨c9r20targets, c9r20choice, ?_, checked⟩
    intro S h
    simp only [c9r20targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 1 _ (by rfl)
  have c9r21_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1)] := by
    let c9r21targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1),(3,1)]]
    let c9r21choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,0),(15,(0,0))),((2,2),(16,(0,0))),((3,1),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r21targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1)] c9r21choice = true := by decide
    refine ⟨c9r21targets, c9r21choice, ?_, checked⟩
    intro S h
    simp only [c9r21targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 4 _ (by rfl)
  have c9r22_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3)] := by
    let c9r22targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,3)]]
    let c9r22choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((1,6),(13,(0,0))),((2,2),(14,(0,0))),((2,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r22targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3)] c9r22choice = true := by decide
    refine ⟨c9r22targets, c9r22choice, ?_, checked⟩
    intro S h
    simp only [c9r22targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 9 _ (by rfl)
  have c9r23_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4)] := by
    let c9r23targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(2,4)]]
    let c9r23choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,3),(11,(0,0))),((1,5),(12,(0,0))),((1,6),(13,(0,0))),((2,2),(14,(0,0))),((2,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r23targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4)] c9r23choice = true := by decide
    refine ⟨c9r23targets, c9r23choice, ?_, checked⟩
    intro S h
    simp only [c9r23targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r16_closed
  · subst row; exact c9r17_closed
  · subst row; exact c9r18_closed
  · subst row; exact c9r19_closed
  · subst row; exact c9r20_closed
  · subst row; exact c9r21_closed
  · subst row; exact c9r22_closed
  · subst row; exact c9r23_closed
theorem C9R00000G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r24_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5)] := by
    let c9r24targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5),(2,5)]]
    let c9r24choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,6),(13,(0,0))),((2,2),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r24targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5)] c9r24choice = true := by decide
    refine ⟨c9r24targets, c9r24choice, ?_, checked⟩
    intro S h
    simp only [c9r24targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 16 _ (by rfl)
  have c9r25_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6)] := by
    let c9r25targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6),(2,6)]]
    let c9r25choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,7),(14,(0,0))),((2,2),(15,(0,0))),((2,6),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r25targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6)] c9r25choice = true := by decide
    refine ⟨c9r25targets, c9r25choice, ?_, checked⟩
    intro S h
    simp only [c9r25targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 19 _ (by rfl)
  have c9r26_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,2)] := by
    let c9r26targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,2),(3,2)]]
    let c9r26choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,1),(15,(0,0))),((2,3),(16,(0,0))),((3,2),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r26targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,2)] c9r26choice = true := by decide
    refine ⟨c9r26targets, c9r26choice, ?_, checked⟩
    intro S h
    simp only [c9r26targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 22 _ (by rfl)
  have c9r27_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4)] := by
    let c9r27targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(2,4)]]
    let c9r27choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,5),(12,(0,0))),((1,6),(13,(0,0))),((2,3),(14,(0,0))),((2,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r27targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4)] c9r27choice = true := by decide
    refine ⟨c9r27targets, c9r27choice, ?_, checked⟩
    intro S h
    simp only [c9r27targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 26 _ (by rfl)
  have c9r28_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5)] := by
    let c9r28targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5),(2,5)]]
    let c9r28choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,4),(12,(0,0))),((1,6),(13,(0,0))),((2,3),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r28targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5)] c9r28choice = true := by decide
    refine ⟨c9r28targets, c9r28choice, ?_, checked⟩
    intro S h
    simp only [c9r28targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 29 _ (by rfl)
  have c9r29_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6)] := by
    let c9r29targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6),(2,6)]]
    let c9r29choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,7),(14,(0,0))),((2,3),(15,(0,0))),((2,6),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r29targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6)] c9r29choice = true := by decide
    refine ⟨c9r29targets, c9r29choice, ?_, checked⟩
    intro S h
    simp only [c9r29targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 0 _ (by rfl)
  have c9r30_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,3)] := by
    let c9r30targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,3),(3,3)]]
    let c9r30choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,2),(15,(0,0))),((2,4),(16,(0,0))),((3,3),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r30targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,3)] c9r30choice = true := by decide
    refine ⟨c9r30targets, c9r30choice, ?_, checked⟩
    intro S h
    simp only [c9r30targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 3 _ (by rfl)
  have c9r31_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5)] := by
    let c9r31targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(2,5)]]
    let c9r31choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,6),(13,(0,0))),((2,4),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r31targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5)] c9r31choice = true := by decide
    refine ⟨c9r31targets, c9r31choice, ?_, checked⟩
    intro S h
    simp only [c9r31targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,false,true,false,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r24_closed
  · subst row; exact c9r25_closed
  · subst row; exact c9r26_closed
  · subst row; exact c9r27_closed
  · subst row; exact c9r28_closed
  · subst row; exact c9r29_closed
  · subst row; exact c9r30_closed
  · subst row; exact c9r31_closed
theorem C9R00000_closed (row : List GridPoint) (h : FamilyMember row F9B000L0) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L0, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R00000G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00000G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00000G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00000G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00000G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00000G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00000G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00000G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00000G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00000G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00000G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00000G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00000G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00000G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00000G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00000G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00000G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00000G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00000G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00000G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00000G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00000G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00000G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00000G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00000G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00000G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00000G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00000G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00000G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00000G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00000G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00000G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
