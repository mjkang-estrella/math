import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R00224G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r224_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2)] := by
    let c9r224targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2),(3,2)]]
    let c9r224choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,6),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((3,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r224targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2)] c9r224choice = true := by decide
    refine ⟨c9r224targets, c9r224choice, ?_, checked⟩
    intro S h
    simp only [c9r224targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 22 _ (by rfl)
  have c9r225_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4)] := by
    let c9r225targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4),(3,4)]]
    let c9r225choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,6),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r225targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4)] c9r225choice = true := by decide
    refine ⟨c9r225targets, c9r225choice, ?_, checked⟩
    intro S h
    simp only [c9r225targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 25 _ (by rfl)
  have c9r226_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,5)] := by
    let c9r226targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,5),(3,5)]]
    let c9r226choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,6),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((2,6),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r226targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,5)] c9r226choice = true := by decide
    refine ⟨c9r226targets, c9r226choice, ?_, checked⟩
    intro S h
    simp only [c9r226targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 27 _ (by rfl)
  have c9r227_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2)] := by
    let c9r227targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(3,2)]]
    let c9r227choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((3,1),(14,(0,0))),((3,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r227targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2)] c9r227choice = true := by decide
    refine ⟨c9r227targets, c9r227choice, ?_, checked⟩
    intro S h
    simp only [c9r227targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 0 _ (by rfl)
  have c9r228_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3)] := by
    let c9r228targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3),(3,3)]]
    let c9r228choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r228targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3)] c9r228choice = true := by decide
    refine ⟨c9r228targets, c9r228choice, ?_, checked⟩
    intro S h
    simp only [c9r228targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 3 _ (by rfl)
  have c9r229_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4)] := by
    let c9r229targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4),(3,4)]]
    let c9r229choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,2),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r229targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4)] c9r229choice = true := by decide
    refine ⟨c9r229targets, c9r229choice, ?_, checked⟩
    intro S h
    simp only [c9r229targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 6 _ (by rfl)
  have c9r230_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2)] := by
    let c9r230targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2),(4,2)]]
    let c9r230choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((3,1),(14,(0,0))),((3,3),(15,(0,0))),((4,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r230targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2)] c9r230choice = true := by decide
    refine ⟨c9r230targets, c9r230choice, ?_, checked⟩
    intro S h
    simp only [c9r230targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 9 _ (by rfl)
  have c9r231_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4)] := by
    let c9r231targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4),(3,4)]]
    let c9r231choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r231targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4)] c9r231choice = true := by decide
    refine ⟨c9r231targets, c9r231choice, ?_, checked⟩
    intro S h
    simp only [c9r231targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 12 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r224_closed
  · subst row; exact c9r225_closed
  · subst row; exact c9r226_closed
  · subst row; exact c9r227_closed
  · subst row; exact c9r228_closed
  · subst row; exact c9r229_closed
  · subst row; exact c9r230_closed
  · subst row; exact c9r231_closed
theorem C9R00224G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r232_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5)] := by
    let c9r232targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5),(3,5)]]
    let c9r232choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,6),(13,(0,0))),((3,4),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r232targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5)] c9r232choice = true := by decide
    refine ⟨c9r232targets, c9r232choice, ?_, checked⟩
    intro S h
    simp only [c9r232targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 15 _ (by rfl)
  have c9r233_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4)] := by
    let c9r233targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4),(4,4)]]
    let c9r233choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,3),(14,(0,0))),((3,5),(15,(0,0))),((4,4),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r233targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4)] c9r233choice = true := by decide
    refine ⟨c9r233targets, c9r233choice, ?_, checked⟩
    intro S h
    simp only [c9r233targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 18 _ (by rfl)
  have c9r234_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)] := by
    let c9r234targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)]]
    let c9r234choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,-1),(11,(0,1))),((2,3),(12,(0,0))),((3,0),(13,(0,0))),((3,1),(14,(0,0))),((3,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r234targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)] c9r234choice = true := by decide
    refine ⟨c9r234targets, c9r234choice, ?_, checked⟩
    intro S h
    simp only [c9r234targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 22 _ (by rfl)
  have c9r235_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3)] := by
    let c9r235targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,3)]]
    let c9r235choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0))),((3,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r235targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3)] c9r235choice = true := by decide
    refine ⟨c9r235targets, c9r235choice, ?_, checked⟩
    intro S h
    simp only [c9r235targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 26 _ (by rfl)
  have c9r236_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1)] := by
    let c9r236targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,1)]]
    let c9r236choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((3,0),(13,(0,0))),((3,2),(14,(0,0))),((4,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r236targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1)] c9r236choice = true := by decide
    refine ⟨c9r236targets, c9r236choice, ?_, checked⟩
    intro S h
    simp only [c9r236targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 29 _ (by rfl)
  have c9r237_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2)] := by
    let c9r237targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2),(4,2)]]
    let c9r237choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0))),((3,1),(13,(0,0))),((3,3),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r237targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2)] c9r237choice = true := by decide
    refine ⟨c9r237targets, c9r237choice, ?_, checked⟩
    intro S h
    simp only [c9r237targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 31 _ (by rfl)
  have c9r238_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4)] := by
    let c9r238targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4),(3,4)]]
    let c9r238choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,5),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r238targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4)] c9r238choice = true := by decide
    refine ⟨c9r238targets, c9r238choice, ?_, checked⟩
    intro S h
    simp only [c9r238targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 3 _ (by rfl)
  have c9r239_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2)] := by
    let c9r239targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2),(4,2)]]
    let c9r239choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0))),((3,3),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r239targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2)] c9r239choice = true := by decide
    refine ⟨c9r239targets, c9r239choice, ?_, checked⟩
    intro S h
    simp only [c9r239targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r232_closed
  · subst row; exact c9r233_closed
  · subst row; exact c9r234_closed
  · subst row; exact c9r235_closed
  · subst row; exact c9r236_closed
  · subst row; exact c9r237_closed
  · subst row; exact c9r238_closed
  · subst row; exact c9r239_closed
theorem C9R00224G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r240_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,3)] := by
    let c9r240targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,3),(4,3)]]
    let c9r240choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,4),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r240targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,3)] c9r240choice = true := by decide
    refine ⟨c9r240targets, c9r240choice, ?_, checked⟩
    intro S h
    simp only [c9r240targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 8 _ (by rfl)
  have c9r241_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2)] := by
    let c9r241targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,2)]]
    let c9r241choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((3,0),(13,(0,0))),((3,3),(14,(0,0))),((4,1),(15,(0,0))),((4,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r241targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2)] c9r241choice = true := by decide
    refine ⟨c9r241targets, c9r241choice, ?_, checked⟩
    intro S h
    simp only [c9r241targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 12 _ (by rfl)
  have c9r242_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3)] := by
    let c9r242targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3),(4,3)]]
    let c9r242choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((3,1),(13,(0,0))),((3,4),(14,(0,0))),((4,2),(15,(0,0))),((4,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r242targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3)] c9r242choice = true := by decide
    refine ⟨c9r242targets, c9r242choice, ?_, checked⟩
    intro S h
    simp only [c9r242targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 15 _ (by rfl)
  have c9r243_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2)] := by
    let c9r243targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2),(5,2)]]
    let c9r243choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((3,1),(13,(0,0))),((3,3),(14,(0,0))),((4,1),(15,(0,0))),((4,3),(16,(0,0))),((5,2),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r243targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2)] c9r243choice = true := by decide
    refine ⟨c9r243targets, c9r243choice, ?_, checked⟩
    intro S h
    simp only [c9r243targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 18 _ (by rfl)
  have c9r244_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6)] := by
    let c9r244targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c9r244choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,7),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r244targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6)] c9r244choice = true := by decide
    refine ⟨c9r244targets, c9r244choice, ?_, checked⟩
    intro S h
    simp only [c9r244targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 23 _ (by rfl)
  have c9r245_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3)] := by
    let c9r245targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,3)]]
    let c9r245choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,6),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r245targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3)] c9r245choice = true := by decide
    refine ⟨c9r245targets, c9r245choice, ?_, checked⟩
    intro S h
    simp only [c9r245targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 27 _ (by rfl)
  have c9r246_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4)] := by
    let c9r246targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(3,4)]]
    let c9r246choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,6),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r246targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4)] c9r246choice = true := by decide
    refine ⟨c9r246targets, c9r246choice, ?_, checked⟩
    intro S h
    simp only [c9r246targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 29 _ (by rfl)
  have c9r247_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5)] := by
    let c9r247targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5),(3,5)]]
    let c9r247choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,6),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,6),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r247targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5)] c9r247choice = true := by decide
    refine ⟨c9r247targets, c9r247choice, ?_, checked⟩
    intro S h
    simp only [c9r247targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r240_closed
  · subst row; exact c9r241_closed
  · subst row; exact c9r242_closed
  · subst row; exact c9r243_closed
  · subst row; exact c9r244_closed
  · subst row; exact c9r245_closed
  · subst row; exact c9r246_closed
  · subst row; exact c9r247_closed
theorem C9R00224G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r248_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3)] := by
    let c9r248targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,3)]]
    let c9r248choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r248targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3)] c9r248choice = true := by decide
    refine ⟨c9r248targets, c9r248choice, ?_, checked⟩
    intro S h
    simp only [c9r248targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 3 _ (by rfl)
  have c9r249_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)] := by
    let c9r249targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(3,4)]]
    let c9r249choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r249targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)] c9r249choice = true := by decide
    refine ⟨c9r249targets, c9r249choice, ?_, checked⟩
    intro S h
    simp only [c9r249targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 6 _ (by rfl)
  have c9r250_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3)] := by
    let c9r250targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3),(4,3)]]
    let c9r250choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0))),((3,4),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r250targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3)] c9r250choice = true := by decide
    refine ⟨c9r250targets, c9r250choice, ?_, checked⟩
    intro S h
    simp only [c9r250targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 9 _ (by rfl)
  have c9r251_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5)] := by
    let c9r251targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(3,5)]]
    let c9r251choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,5),(10,(0,0))),((2,3),(11,(0,0))),((2,6),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r251targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5)] c9r251choice = true := by decide
    refine ⟨c9r251targets, c9r251choice, ?_, checked⟩
    intro S h
    simp only [c9r251targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 12 _ (by rfl)
  have c9r252_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4)] := by
    let c9r252targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4),(4,4)]]
    let c9r252choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,5),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,3),(13,(0,0))),((3,5),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r252targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4)] c9r252choice = true := by decide
    refine ⟨c9r252targets, c9r252choice, ?_, checked⟩
    intro S h
    simp only [c9r252targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 15 _ (by rfl)
  have c9r253_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3)] := by
    let c9r253targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c9r253choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0))),((3,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r253targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3)] c9r253choice = true := by decide
    refine ⟨c9r253targets, c9r253choice, ?_, checked⟩
    intro S h
    simp only [c9r253targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 21 _ (by rfl)
  have c9r254_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4)] := by
    let c9r254targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,4)]]
    let c9r254choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,5),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r254targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4)] c9r254choice = true := by decide
    refine ⟨c9r254targets, c9r254choice, ?_, checked⟩
    intro S h
    simp only [c9r254targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 25 _ (by rfl)
  have c9r255_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,2)] := by
    let c9r255targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,2)]]
    let c9r255choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0))),((3,1),(13,(0,0))),((3,3),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r255targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,2)] c9r255choice = true := by decide
    refine ⟨c9r255targets, c9r255choice, ?_, checked⟩
    intro S h
    simp only [c9r255targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,false,true,true,false,true,true] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r248_closed
  · subst row; exact c9r249_closed
  · subst row; exact c9r250_closed
  · subst row; exact c9r251_closed
  · subst row; exact c9r252_closed
  · subst row; exact c9r253_closed
  · subst row; exact c9r254_closed
  · subst row; exact c9r255_closed
theorem C9R00224_closed (row : List GridPoint) (h : FamilyMember row F9B000L7) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L7, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R00224G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00224G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00224G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00224G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00224G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00224G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00224G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00224G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00224G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00224G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00224G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00224G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00224G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00224G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00224G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00224G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00224G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00224G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00224G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00224G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00224G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00224G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00224G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00224G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00224G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00224G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00224G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00224G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00224G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00224G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00224G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00224G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
