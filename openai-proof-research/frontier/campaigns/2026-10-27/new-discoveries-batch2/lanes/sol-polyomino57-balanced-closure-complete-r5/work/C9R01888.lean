import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R01888G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1888_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r1888targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,5),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r1888choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,5),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1888targets [(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)] c9r1888choice = true := by decide
    refine ⟨c9r1888targets, c9r1888choice, ?_, checked⟩
    intro S h
    simp only [c9r1888targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 7 _ (by rfl)
  have c9r1889_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r1889targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,6),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,5),(1,6),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r1889choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,6),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1889targets [(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)] c9r1889choice = true := by decide
    refine ⟨c9r1889targets, c9r1889choice, ?_, checked⟩
    intro S h
    simp only [c9r1889targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 15 _ (by rfl)
  have c9r1890_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r1890targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r1890choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1890targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r1890choice = true := by decide
    refine ⟨c9r1890targets, c9r1890choice, ?_, checked⟩
    intro S h
    simp only [c9r1890targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 22 _ (by rfl)
  have c9r1891_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r1891targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r1891choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1891targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r1891choice = true := by decide
    refine ⟨c9r1891targets, c9r1891choice, ?_, checked⟩
    intro S h
    simp only [c9r1891targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 26 _ (by rfl)
  have c9r1892_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r1892targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r1892choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1892targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r1892choice = true := by decide
    refine ⟨c9r1892targets, c9r1892choice, ?_, checked⟩
    intro S h
    simp only [c9r1892targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 29 _ (by rfl)
  have c9r1893_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r1893targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r1893choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1893targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r1893choice = true := by decide
    refine ⟨c9r1893targets, c9r1893choice, ?_, checked⟩
    intro S h
    simp only [c9r1893targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 31 _ (by rfl)
  have c9r1894_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r1894targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r1894choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1894targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r1894choice = true := by decide
    refine ⟨c9r1894targets, c9r1894choice, ?_, checked⟩
    intro S h
    simp only [c9r1894targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 1 _ (by rfl)
  have c9r1895_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r1895targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r1895choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1895targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] c9r1895choice = true := by decide
    refine ⟨c9r1895targets, c9r1895choice, ?_, checked⟩
    intro S h
    simp only [c9r1895targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1888_closed
  · subst row; exact c9r1889_closed
  · subst row; exact c9r1890_closed
  · subst row; exact c9r1891_closed
  · subst row; exact c9r1892_closed
  · subst row; exact c9r1893_closed
  · subst row; exact c9r1894_closed
  · subst row; exact c9r1895_closed
theorem C9R01888G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1896_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c9r1896targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c9r1896choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1896targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] c9r1896choice = true := by decide
    refine ⟨c9r1896targets, c9r1896choice, ?_, checked⟩
    intro S h
    simp only [c9r1896targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 7 _ (by rfl)
  have c9r1897_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c9r1897targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c9r1897choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1897targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] c9r1897choice = true := by decide
    refine ⟨c9r1897targets, c9r1897choice, ?_, checked⟩
    intro S h
    simp only [c9r1897targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 9 _ (by rfl)
  have c9r1898_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c9r1898targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c9r1898choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1898targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] c9r1898choice = true := by decide
    refine ⟨c9r1898targets, c9r1898choice, ?_, checked⟩
    intro S h
    simp only [c9r1898targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 12 _ (by rfl)
  have c9r1899_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c9r1899targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c9r1899choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1899targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] c9r1899choice = true := by decide
    refine ⟨c9r1899targets, c9r1899choice, ?_, checked⟩
    intro S h
    simp only [c9r1899targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 15 _ (by rfl)
  have c9r1900_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c9r1900targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c9r1900choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1900targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] c9r1900choice = true := by decide
    refine ⟨c9r1900targets, c9r1900choice, ?_, checked⟩
    intro S h
    simp only [c9r1900targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 18 _ (by rfl)
  have c9r1901_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c9r1901targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c9r1901choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1901targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] c9r1901choice = true := by decide
    refine ⟨c9r1901targets, c9r1901choice, ?_, checked⟩
    intro S h
    simp only [c9r1901targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 21 _ (by rfl)
  have c9r1902_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)] := by
    let c9r1902targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c9r1902choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1902targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)] c9r1902choice = true := by decide
    refine ⟨c9r1902targets, c9r1902choice, ?_, checked⟩
    intro S h
    simp only [c9r1902targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 26 _ (by rfl)
  have c9r1903_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)] := by
    let c9r1903targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c9r1903choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1903targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)] c9r1903choice = true := by decide
    refine ⟨c9r1903targets, c9r1903choice, ?_, checked⟩
    intro S h
    simp only [c9r1903targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1896_closed
  · subst row; exact c9r1897_closed
  · subst row; exact c9r1898_closed
  · subst row; exact c9r1899_closed
  · subst row; exact c9r1900_closed
  · subst row; exact c9r1901_closed
  · subst row; exact c9r1902_closed
  · subst row; exact c9r1903_closed
theorem C9R01888G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1904_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)] := by
    let c9r1904targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c9r1904choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1904targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)] c9r1904choice = true := by decide
    refine ⟨c9r1904targets, c9r1904choice, ?_, checked⟩
    intro S h
    simp only [c9r1904targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 30 _ (by rfl)
  have c9r1905_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)] := by
    let c9r1905targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
    let c9r1905choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1905targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)] c9r1905choice = true := by decide
    refine ⟨c9r1905targets, c9r1905choice, ?_, checked⟩
    intro S h
    simp only [c9r1905targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 1 _ (by rfl)
  have c9r1906_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)] := by
    let c9r1906targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
    let c9r1906choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1906targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)] c9r1906choice = true := by decide
    refine ⟨c9r1906targets, c9r1906choice, ?_, checked⟩
    intro S h
    simp only [c9r1906targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 3 _ (by rfl)
  have c9r1907_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)] := by
    let c9r1907targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1907choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1907targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)] c9r1907choice = true := by decide
    refine ⟨c9r1907targets, c9r1907choice, ?_, checked⟩
    intro S h
    simp only [c9r1907targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 7 _ (by rfl)
  have c9r1908_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)] := by
    let c9r1908targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c9r1908choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1908targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)] c9r1908choice = true := by decide
    refine ⟨c9r1908targets, c9r1908choice, ?_, checked⟩
    intro S h
    simp only [c9r1908targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 10 _ (by rfl)
  have c9r1909_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)] := by
    let c9r1909targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c9r1909choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1909targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)] c9r1909choice = true := by decide
    refine ⟨c9r1909targets, c9r1909choice, ?_, checked⟩
    intro S h
    simp only [c9r1909targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 12 _ (by rfl)
  have c9r1910_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)] := by
    let c9r1910targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c9r1910choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1910targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)] c9r1910choice = true := by decide
    refine ⟨c9r1910targets, c9r1910choice, ?_, checked⟩
    intro S h
    simp only [c9r1910targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
  have c9r1911_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)] := by
    let c9r1911targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c9r1911choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1911targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)] c9r1911choice = true := by decide
    refine ⟨c9r1911targets, c9r1911choice, ?_, checked⟩
    intro S h
    simp only [c9r1911targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 18 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1904_closed
  · subst row; exact c9r1905_closed
  · subst row; exact c9r1906_closed
  · subst row; exact c9r1907_closed
  · subst row; exact c9r1908_closed
  · subst row; exact c9r1909_closed
  · subst row; exact c9r1910_closed
  · subst row; exact c9r1911_closed
theorem C9R01888G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1912_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)] := by
    let c9r1912targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c9r1912choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1912targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)] c9r1912choice = true := by decide
    refine ⟨c9r1912targets, c9r1912choice, ?_, checked⟩
    intro S h
    simp only [c9r1912targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 21 _ (by rfl)
  have c9r1913_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r1913targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r1913choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1913targets [(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)] c9r1913choice = true := by decide
    refine ⟨c9r1913targets, c9r1913choice, ?_, checked⟩
    intro S h
    simp only [c9r1913targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 26 _ (by rfl)
  have c9r1914_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r1914targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r1914choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,6),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1914targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r1914choice = true := by decide
    refine ⟨c9r1914targets, c9r1914choice, ?_, checked⟩
    intro S h
    simp only [c9r1914targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 0 _ (by rfl)
  have c9r1915_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c9r1915targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c9r1915choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1915targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)] c9r1915choice = true := by decide
    refine ⟨c9r1915targets, c9r1915choice, ?_, checked⟩
    intro S h
    simp only [c9r1915targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 5 _ (by rfl)
  have c9r1916_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r1916targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r1916choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1916targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)] c9r1916choice = true := by decide
    refine ⟨c9r1916targets, c9r1916choice, ?_, checked⟩
    intro S h
    simp only [c9r1916targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 8 _ (by rfl)
  have c9r1917_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r1917targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r1917choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1917targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)] c9r1917choice = true := by decide
    refine ⟨c9r1917targets, c9r1917choice, ?_, checked⟩
    intro S h
    simp only [c9r1917targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 10 _ (by rfl)
  have c9r1918_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r1918targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r1918choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,5),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1918targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r1918choice = true := by decide
    refine ⟨c9r1918targets, c9r1918choice, ?_, checked⟩
    intro S h
    simp only [c9r1918targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 12 _ (by rfl)
  have c9r1919_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r1919targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r1919choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1919targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r1919choice = true := by decide
    refine ⟨c9r1919targets, c9r1919choice, ?_, checked⟩
    intro S h
    simp only [c9r1919targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,false,true,true] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1912_closed
  · subst row; exact c9r1913_closed
  · subst row; exact c9r1914_closed
  · subst row; exact c9r1915_closed
  · subst row; exact c9r1916_closed
  · subst row; exact c9r1917_closed
  · subst row; exact c9r1918_closed
  · subst row; exact c9r1919_closed
theorem C9R01888_closed (row : List GridPoint) (h : FamilyMember row F9B000L59) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L59, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R01888G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01888G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01888G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01888G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01888G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01888G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01888G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01888G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01888G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01888G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01888G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01888G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01888G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01888G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01888G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01888G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01888G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01888G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01888G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01888G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01888G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01888G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01888G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01888G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01888G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01888G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01888G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01888G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01888G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01888G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01888G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01888G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
