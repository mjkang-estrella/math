import F10All
import F9B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R00960G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r960_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r960targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r960choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r960targets [(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)] c9r960choice = true := by decide
    refine ⟨c9r960targets, c9r960choice, ?_, checked⟩
    intro S h
    simp only [c9r960targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 15 _ (by rfl)
  have c9r961_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r961targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r961choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r961targets [(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)] c9r961choice = true := by decide
    refine ⟨c9r961targets, c9r961choice, ?_, checked⟩
    intro S h
    simp only [c9r961targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 17 _ (by rfl)
  have c9r962_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r962targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r962choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r962targets [(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)] c9r962choice = true := by decide
    refine ⟨c9r962targets, c9r962choice, ?_, checked⟩
    intro S h
    simp only [c9r962targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 19 _ (by rfl)
  have c9r963_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r963targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r963choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,5),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r963targets [(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)] c9r963choice = true := by decide
    refine ⟨c9r963targets, c9r963choice, ?_, checked⟩
    intro S h
    simp only [c9r963targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 27 _ (by rfl)
  have c9r964_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r964targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r964choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,5),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r964targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r964choice = true := by decide
    refine ⟨c9r964targets, c9r964choice, ?_, checked⟩
    intro S h
    simp only [c9r964targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 2 _ (by rfl)
  have c9r965_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r965targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r965choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r965targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r965choice = true := by decide
    refine ⟨c9r965targets, c9r965choice, ?_, checked⟩
    intro S h
    simp only [c9r965targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 6 _ (by rfl)
  have c9r966_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r966targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r966choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r966targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r966choice = true := by decide
    refine ⟨c9r966targets, c9r966choice, ?_, checked⟩
    intro S h
    simp only [c9r966targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 9 _ (by rfl)
  have c9r967_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r967targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r967choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r967targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r967choice = true := by decide
    refine ⟨c9r967targets, c9r967choice, ?_, checked⟩
    intro S h
    simp only [c9r967targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r960_closed
  · subst row; exact c9r961_closed
  · subst row; exact c9r962_closed
  · subst row; exact c9r963_closed
  · subst row; exact c9r964_closed
  · subst row; exact c9r965_closed
  · subst row; exact c9r966_closed
  · subst row; exact c9r967_closed
theorem C9R00960G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r968_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r968targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r968choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r968targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r968choice = true := by decide
    refine ⟨c9r968targets, c9r968choice, ?_, checked⟩
    intro S h
    simp only [c9r968targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 13 _ (by rfl)
  have c9r969_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r969targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r969choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r969targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)] c9r969choice = true := by decide
    refine ⟨c9r969targets, c9r969choice, ?_, checked⟩
    intro S h
    simp only [c9r969targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 16 _ (by rfl)
  have c9r970_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c9r970targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c9r970choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r970targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)] c9r970choice = true := by decide
    refine ⟨c9r970targets, c9r970choice, ?_, checked⟩
    intro S h
    simp only [c9r970targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 19 _ (by rfl)
  have c9r971_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c9r971targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c9r971choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r971targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)] c9r971choice = true := by decide
    refine ⟨c9r971targets, c9r971choice, ?_, checked⟩
    intro S h
    simp only [c9r971targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 21 _ (by rfl)
  have c9r972_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c9r972targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c9r972choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r972targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)] c9r972choice = true := by decide
    refine ⟨c9r972targets, c9r972choice, ?_, checked⟩
    intro S h
    simp only [c9r972targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 24 _ (by rfl)
  have c9r973_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c9r973targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c9r973choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r973targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)] c9r973choice = true := by decide
    refine ⟨c9r973targets, c9r973choice, ?_, checked⟩
    intro S h
    simp only [c9r973targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 27 _ (by rfl)
  have c9r974_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c9r974targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c9r974choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r974targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)] c9r974choice = true := by decide
    refine ⟨c9r974targets, c9r974choice, ?_, checked⟩
    intro S h
    simp only [c9r974targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 30 _ (by rfl)
  have c9r975_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c9r975targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c9r975choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r975targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)] c9r975choice = true := by decide
    refine ⟨c9r975targets, c9r975choice, ?_, checked⟩
    intro S h
    simp only [c9r975targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r968_closed
  · subst row; exact c9r969_closed
  · subst row; exact c9r970_closed
  · subst row; exact c9r971_closed
  · subst row; exact c9r972_closed
  · subst row; exact c9r973_closed
  · subst row; exact c9r974_closed
  · subst row; exact c9r975_closed
theorem C9R00960G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r976_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] := by
    let c9r976targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c9r976choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r976targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] c9r976choice = true := by decide
    refine ⟨c9r976targets, c9r976choice, ?_, checked⟩
    intro S h
    simp only [c9r976targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 6 _ (by rfl)
  have c9r977_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] := by
    let c9r977targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c9r977choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r977targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] c9r977choice = true := by decide
    refine ⟨c9r977targets, c9r977choice, ?_, checked⟩
    intro S h
    simp only [c9r977targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 8 _ (by rfl)
  have c9r978_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] := by
    let c9r978targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c9r978choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r978targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] c9r978choice = true := by decide
    refine ⟨c9r978targets, c9r978choice, ?_, checked⟩
    intro S h
    simp only [c9r978targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 10 _ (by rfl)
  have c9r979_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] := by
    let c9r979targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
    let c9r979choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r979targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] c9r979choice = true := by decide
    refine ⟨c9r979targets, c9r979choice, ?_, checked⟩
    intro S h
    simp only [c9r979targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 13 _ (by rfl)
  have c9r980_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] := by
    let c9r980targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
    let c9r980choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,-1),(13,(0,1))),((5,1),(14,(0,0))),((6,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r980targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] c9r980choice = true := by decide
    refine ⟨c9r980targets, c9r980choice, ?_, checked⟩
    intro S h
    simp only [c9r980targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 15 _ (by rfl)
  have c9r981_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] := by
    let c9r981targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c9r981choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r981targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] c9r981choice = true := by decide
    refine ⟨c9r981targets, c9r981choice, ?_, checked⟩
    intro S h
    simp only [c9r981targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 19 _ (by rfl)
  have c9r982_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] := by
    let c9r982targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c9r982choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r982targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] c9r982choice = true := by decide
    refine ⟨c9r982targets, c9r982choice, ?_, checked⟩
    intro S h
    simp only [c9r982targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 22 _ (by rfl)
  have c9r983_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] := by
    let c9r983targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c9r983choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r983targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] c9r983choice = true := by decide
    refine ⟨c9r983targets, c9r983choice, ?_, checked⟩
    intro S h
    simp only [c9r983targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r976_closed
  · subst row; exact c9r977_closed
  · subst row; exact c9r978_closed
  · subst row; exact c9r979_closed
  · subst row; exact c9r980_closed
  · subst row; exact c9r981_closed
  · subst row; exact c9r982_closed
  · subst row; exact c9r983_closed
theorem C9R00960G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r984_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] := by
    let c9r984targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c9r984choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r984targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] c9r984choice = true := by decide
    refine ⟨c9r984targets, c9r984choice, ?_, checked⟩
    intro S h
    simp only [c9r984targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 27 _ (by rfl)
  have c9r985_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] := by
    let c9r985targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c9r985choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r985targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] c9r985choice = true := by decide
    refine ⟨c9r985targets, c9r985choice, ?_, checked⟩
    intro S h
    simp only [c9r985targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 30 _ (by rfl)
  have c9r986_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] := by
    let c9r986targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c9r986choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,2),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r986targets [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] c9r986choice = true := by decide
    refine ⟨c9r986targets, c9r986choice, ?_, checked⟩
    intro S h
    simp only [c9r986targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 1 _ (by rfl)
  have c9r987_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r987targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r987choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,6),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0))),((3,4),(15,(0,0))),((3,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r987targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r987choice = true := by decide
    refine ⟨c9r987targets, c9r987choice, ?_, checked⟩
    intro S h
    simp only [c9r987targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 7 _ (by rfl)
  have c9r988_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c9r988targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c9r988choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,5),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0))),((4,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r988targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)] c9r988choice = true := by decide
    refine ⟨c9r988targets, c9r988choice, ?_, checked⟩
    intro S h
    simp only [c9r988targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 12 _ (by rfl)
  have c9r989_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r989targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r989choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,5),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r989targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)] c9r989choice = true := by decide
    refine ⟨c9r989targets, c9r989choice, ?_, checked⟩
    intro S h
    simp only [c9r989targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 15 _ (by rfl)
  have c9r990_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r990targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r990choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,5),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r990targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)] c9r990choice = true := by decide
    refine ⟨c9r990targets, c9r990choice, ?_, checked⟩
    intro S h
    simp only [c9r990targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 17 _ (by rfl)
  have c9r991_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r991targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r991choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,5),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,5),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r991targets [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r991choice = true := by decide
    refine ⟨c9r991targets, c9r991choice, ?_, checked⟩
    intro S h
    simp only [c9r991targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,false] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r984_closed
  · subst row; exact c9r985_closed
  · subst row; exact c9r986_closed
  · subst row; exact c9r987_closed
  · subst row; exact c9r988_closed
  · subst row; exact c9r989_closed
  · subst row; exact c9r990_closed
  · subst row; exact c9r991_closed
theorem C9R00960_closed (row : List GridPoint) (h : FamilyMember row F9B000L30) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B000L30, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R00960G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00960G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00960G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00960G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00960G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00960G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00960G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00960G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00960G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00960G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00960G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00960G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00960G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00960G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00960G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00960G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00960G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00960G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00960G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00960G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00960G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00960G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00960G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00960G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R00960G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R00960G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R00960G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R00960G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R00960G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R00960G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R00960G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R00960G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
