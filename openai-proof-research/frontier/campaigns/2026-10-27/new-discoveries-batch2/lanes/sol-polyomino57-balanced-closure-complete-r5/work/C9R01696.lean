import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R01696G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1696_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r1696targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r1696choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1696targets [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)] c9r1696choice = true := by decide
    refine ⟨c9r1696targets, c9r1696choice, ?_, checked⟩
    intro S h
    simp only [c9r1696targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 4 _ (by rfl)
  have c9r1697_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r1697targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r1697choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,-1),(11,(0,1))),((3,3),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0))),((4,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1697targets [(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r1697choice = true := by decide
    refine ⟨c9r1697targets, c9r1697choice, ?_, checked⟩
    intro S h
    simp only [c9r1697targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 9 _ (by rfl)
  have c9r1698_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r1698targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1698choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1698targets [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r1698choice = true := by decide
    refine ⟨c9r1698targets, c9r1698choice, ?_, checked⟩
    intro S h
    simp only [c9r1698targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 14 _ (by rfl)
  have c9r1699_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r1699targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r1699choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,3),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((5,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1699targets [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r1699choice = true := by decide
    refine ⟨c9r1699targets, c9r1699choice, ?_, checked⟩
    intro S h
    simp only [c9r1699targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 17 _ (by rfl)
  have c9r1700_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r1700targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r1700choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1700targets [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r1700choice = true := by decide
    refine ⟨c9r1700targets, c9r1700choice, ?_, checked⟩
    intro S h
    simp only [c9r1700targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 19 _ (by rfl)
  have c9r1701_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r1701targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r1701choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1701targets [(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r1701choice = true := by decide
    refine ⟨c9r1701targets, c9r1701choice, ?_, checked⟩
    intro S h
    simp only [c9r1701targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 21 _ (by rfl)
  have c9r1702_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r1702targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r1702choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,-1),(11,(0,1))),((3,4),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0))),((4,2),(15,(0,0))),((4,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1702targets [(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r1702choice = true := by decide
    refine ⟨c9r1702targets, c9r1702choice, ?_, checked⟩
    intro S h
    simp only [c9r1702targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 28 _ (by rfl)
  have c9r1703_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r1703targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r1703choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,-1),(11,(0,1))),((3,5),(12,(0,0))),((4,0),(13,(0,0))),((4,1),(14,(0,0))),((4,2),(15,(0,0))),((4,3),(16,(0,0))),((4,4),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1703targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r1703choice = true := by decide
    refine ⟨c9r1703targets, c9r1703choice, ?_, checked⟩
    intro S h
    simp only [c9r1703targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 3 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1696_closed
  · subst row; exact c9r1697_closed
  · subst row; exact c9r1698_closed
  · subst row; exact c9r1699_closed
  · subst row; exact c9r1700_closed
  · subst row; exact c9r1701_closed
  · subst row; exact c9r1702_closed
  · subst row; exact c9r1703_closed
theorem C9R01696G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1704_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r1704targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r1704choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,4),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0))),((5,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1704targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r1704choice = true := by decide
    refine ⟨c9r1704targets, c9r1704choice, ?_, checked⟩
    intro S h
    simp only [c9r1704targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 7 _ (by rfl)
  have c9r1705_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r1705targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r1705choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0))),((5,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1705targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r1705choice = true := by decide
    refine ⟨c9r1705targets, c9r1705choice, ?_, checked⟩
    intro S h
    simp only [c9r1705targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 10 _ (by rfl)
  have c9r1706_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r1706targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r1706choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1706targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r1706choice = true := by decide
    refine ⟨c9r1706targets, c9r1706choice, ?_, checked⟩
    intro S h
    simp only [c9r1706targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 12 _ (by rfl)
  have c9r1707_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r1707targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r1707choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,4),(15,(0,0))),((5,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1707targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r1707choice = true := by decide
    refine ⟨c9r1707targets, c9r1707choice, ?_, checked⟩
    intro S h
    simp only [c9r1707targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 14 _ (by rfl)
  have c9r1708_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r1708targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r1708choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1708targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)] c9r1708choice = true := by decide
    refine ⟨c9r1708targets, c9r1708choice, ?_, checked⟩
    intro S h
    simp only [c9r1708targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 17 _ (by rfl)
  have c9r1709_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c9r1709targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c9r1709choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,0),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1709targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)] c9r1709choice = true := by decide
    refine ⟨c9r1709targets, c9r1709choice, ?_, checked⟩
    intro S h
    simp only [c9r1709targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 20 _ (by rfl)
  have c9r1710_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c9r1710targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c9r1710choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((5,-1),(14,(0,1))),((5,1),(15,(0,0))),((6,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1710targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)] c9r1710choice = true := by decide
    refine ⟨c9r1710targets, c9r1710choice, ?_, checked⟩
    intro S h
    simp only [c9r1710targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 22 _ (by rfl)
  have c9r1711_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r1711targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r1711choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1711targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)] c9r1711choice = true := by decide
    refine ⟨c9r1711targets, c9r1711choice, ?_, checked⟩
    intro S h
    simp only [c9r1711targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 25 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1704_closed
  · subst row; exact c9r1705_closed
  · subst row; exact c9r1706_closed
  · subst row; exact c9r1707_closed
  · subst row; exact c9r1708_closed
  · subst row; exact c9r1709_closed
  · subst row; exact c9r1710_closed
  · subst row; exact c9r1711_closed
theorem C9R01696G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1712_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r1712targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r1712choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,2),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1712targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)] c9r1712choice = true := by decide
    refine ⟨c9r1712targets, c9r1712choice, ?_, checked⟩
    intro S h
    simp only [c9r1712targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 28 _ (by rfl)
  have c9r1713_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r1713targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r1713choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,4),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1713targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)] c9r1713choice = true := by decide
    refine ⟨c9r1713targets, c9r1713choice, ?_, checked⟩
    intro S h
    simp only [c9r1713targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 31 _ (by rfl)
  have c9r1714_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r1714targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r1714choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,1),(14,(0,0))),((5,3),(15,(0,0))),((6,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1714targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r1714choice = true := by decide
    refine ⟨c9r1714targets, c9r1714choice, ?_, checked⟩
    intro S h
    simp only [c9r1714targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 2 _ (by rfl)
  have c9r1715_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r1715targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r1715choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1715targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)] c9r1715choice = true := by decide
    refine ⟨c9r1715targets, c9r1715choice, ?_, checked⟩
    intro S h
    simp only [c9r1715targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 7 _ (by rfl)
  have c9r1716_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r1716targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r1716choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1716targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)] c9r1716choice = true := by decide
    refine ⟨c9r1716targets, c9r1716choice, ?_, checked⟩
    intro S h
    simp only [c9r1716targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 9 _ (by rfl)
  have c9r1717_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r1717targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r1717choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1717targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)] c9r1717choice = true := by decide
    refine ⟨c9r1717targets, c9r1717choice, ?_, checked⟩
    intro S h
    simp only [c9r1717targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 11 _ (by rfl)
  have c9r1718_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)] := by
    let c9r1718targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)]]
    let c9r1718choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1718targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)] c9r1718choice = true := by decide
    refine ⟨c9r1718targets, c9r1718choice, ?_, checked⟩
    intro S h
    simp only [c9r1718targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 14 _ (by rfl)
  have c9r1719_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)] := by
    let c9r1719targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)]]
    let c9r1719choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,-1),(14,(0,1))),((6,1),(15,(0,0))),((7,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1719targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)] c9r1719choice = true := by decide
    refine ⟨c9r1719targets, c9r1719choice, ?_, checked⟩
    intro S h
    simp only [c9r1719targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1712_closed
  · subst row; exact c9r1713_closed
  · subst row; exact c9r1714_closed
  · subst row; exact c9r1715_closed
  · subst row; exact c9r1716_closed
  · subst row; exact c9r1717_closed
  · subst row; exact c9r1718_closed
  · subst row; exact c9r1719_closed
theorem C9R01696G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r1720_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r1720targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r1720choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1720targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)] c9r1720choice = true := by decide
    refine ⟨c9r1720targets, c9r1720choice, ?_, checked⟩
    intro S h
    simp only [c9r1720targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 20 _ (by rfl)
  have c9r1721_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r1721targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r1721choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1721targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)] c9r1721choice = true := by decide
    refine ⟨c9r1721targets, c9r1721choice, ?_, checked⟩
    intro S h
    simp only [c9r1721targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 23 _ (by rfl)
  have c9r1722_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r1722targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r1722choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1722targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)] c9r1722choice = true := by decide
    refine ⟨c9r1722targets, c9r1722choice, ?_, checked⟩
    intro S h
    simp only [c9r1722targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 25 _ (by rfl)
  have c9r1723_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r1723targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r1723choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1723targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)] c9r1723choice = true := by decide
    refine ⟨c9r1723targets, c9r1723choice, ?_, checked⟩
    intro S h
    simp only [c9r1723targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 28 _ (by rfl)
  have c9r1724_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r1724targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r1724choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1724targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)] c9r1724choice = true := by decide
    refine ⟨c9r1724targets, c9r1724choice, ?_, checked⟩
    intro S h
    simp only [c9r1724targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 31 _ (by rfl)
  have c9r1725_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r1725targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r1725choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1725targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)] c9r1725choice = true := by decide
    refine ⟨c9r1725targets, c9r1725choice, ?_, checked⟩
    intro S h
    simp only [c9r1725targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 2 _ (by rfl)
  have c9r1726_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r1726targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r1726choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,-1),(12,(0,1))),((4,3),(13,(0,0))),((5,0),(14,(0,0))),((5,1),(15,(0,0))),((5,2),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1726targets [(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)] c9r1726choice = true := by decide
    refine ⟨c9r1726targets, c9r1726choice, ?_, checked⟩
    intro S h
    simp only [c9r1726targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 7 _ (by rfl)
  have c9r1727_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r1727targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r1727choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,-1),(12,(0,1))),((4,4),(13,(0,0))),((5,0),(14,(0,0))),((5,1),(15,(0,0))),((5,2),(16,(0,0))),((5,3),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r1727targets [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)] c9r1727choice = true := by decide
    refine ⟨c9r1727targets, c9r1727choice, ?_, checked⟩
    intro S h
    simp only [c9r1727targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r1720_closed
  · subst row; exact c9r1721_closed
  · subst row; exact c9r1722_closed
  · subst row; exact c9r1723_closed
  · subst row; exact c9r1724_closed
  · subst row; exact c9r1725_closed
  · subst row; exact c9r1726_closed
  · subst row; exact c9r1727_closed
theorem C9R01696_closed (row : List GridPoint) (h : FamilyMember row F9B000L53) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L53, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R01696G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01696G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01696G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01696G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01696G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01696G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01696G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01696G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01696G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01696G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01696G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01696G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01696G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01696G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01696G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01696G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01696G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01696G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01696G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01696G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01696G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01696G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01696G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01696G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R01696G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R01696G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R01696G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R01696G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R01696G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R01696G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R01696G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R01696G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
