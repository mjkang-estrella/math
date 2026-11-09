import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R02016G0 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2016_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c8r2016targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c8r2016choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2016targets [(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)] c8r2016choice = true := by decide
    refine ⟨c8r2016targets, c8r2016choice, ?_, checked⟩
    intro S h
    simp only [c8r2016targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 30 _ (by rfl)
  have c8r2017_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r2017targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r2017choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2017targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)] c8r2017choice = true := by decide
    refine ⟨c8r2017targets, c8r2017choice, ?_, checked⟩
    intro S h
    simp only [c8r2017targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 3 _ (by rfl)
  have c8r2018_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c8r2018targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c8r2018choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2018targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)] c8r2018choice = true := by decide
    refine ⟨c8r2018targets, c8r2018choice, ?_, checked⟩
    intro S h
    simp only [c8r2018targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 5 _ (by rfl)
  have c8r2019_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c8r2019targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c8r2019choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2019targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)] c8r2019choice = true := by decide
    refine ⟨c8r2019targets, c8r2019choice, ?_, checked⟩
    intro S h
    simp only [c8r2019targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 7 _ (by rfl)
  have c8r2020_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c8r2020targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c8r2020choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2020targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)] c8r2020choice = true := by decide
    refine ⟨c8r2020targets, c8r2020choice, ?_, checked⟩
    intro S h
    simp only [c8r2020targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 11 _ (by rfl)
  have c8r2021_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c8r2021targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c8r2021choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2021targets [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] c8r2021choice = true := by decide
    refine ⟨c8r2021targets, c8r2021choice, ?_, checked⟩
    intro S h
    simp only [c8r2021targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 18 _ (by rfl)
  have c8r2022_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r2022targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r2022choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2022targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)] c8r2022choice = true := by decide
    refine ⟨c8r2022targets, c8r2022choice, ?_, checked⟩
    intro S h
    simp only [c8r2022targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 25 _ (by rfl)
  have c8r2023_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r2023targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r2023choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2023targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)] c8r2023choice = true := by decide
    refine ⟨c8r2023targets, c8r2023choice, ?_, checked⟩
    intro S h
    simp only [c8r2023targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2016_closed
  · subst row; exact c8r2017_closed
  · subst row; exact c8r2018_closed
  · subst row; exact c8r2019_closed
  · subst row; exact c8r2020_closed
  · subst row; exact c8r2021_closed
  · subst row; exact c8r2022_closed
  · subst row; exact c8r2023_closed
theorem C8R02016G1 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2024_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r2024targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r2024choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2024targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)] c8r2024choice = true := by decide
    refine ⟨c8r2024targets, c8r2024choice, ?_, checked⟩
    intro S h
    simp only [c8r2024targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 30 _ (by rfl)
  have c8r2025_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r2025targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r2025choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2025targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)] c8r2025choice = true := by decide
    refine ⟨c8r2025targets, c8r2025choice, ?_, checked⟩
    intro S h
    simp only [c8r2025targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 0 _ (by rfl)
  have c8r2026_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r2026targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r2026choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2026targets [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)] c8r2026choice = true := by decide
    refine ⟨c8r2026targets, c8r2026choice, ?_, checked⟩
    intro S h
    simp only [c8r2026targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 5 _ (by rfl)
  have c8r2027_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)] := by
    let c8r2027targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c8r2027choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,-1),(11,(0,1))),((4,3),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2027targets [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)] c8r2027choice = true := by decide
    refine ⟨c8r2027targets, c8r2027choice, ?_, checked⟩
    intro S h
    simp only [c8r2027targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 11 _ (by rfl)
  have c8r2028_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r2028targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r2028choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2028targets [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)] c8r2028choice = true := by decide
    refine ⟨c8r2028targets, c8r2028choice, ?_, checked⟩
    intro S h
    simp only [c8r2028targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 19 _ (by rfl)
  have c8r2029_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r2029targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r2029choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2029targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r2029choice = true := by decide
    refine ⟨c8r2029targets, c8r2029choice, ?_, checked⟩
    intro S h
    simp only [c8r2029targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 28 _ (by rfl)
  have c8r2030_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c8r2030targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c8r2030choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2030targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)] c8r2030choice = true := by decide
    refine ⟨c8r2030targets, c8r2030choice, ?_, checked⟩
    intro S h
    simp only [c8r2030targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 0 _ (by rfl)
  have c8r2031_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r2031targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r2031choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2031targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] c8r2031choice = true := by decide
    refine ⟨c8r2031targets, c8r2031choice, ?_, checked⟩
    intro S h
    simp only [c8r2031targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 3 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2024_closed
  · subst row; exact c8r2025_closed
  · subst row; exact c8r2026_closed
  · subst row; exact c8r2027_closed
  · subst row; exact c8r2028_closed
  · subst row; exact c8r2029_closed
  · subst row; exact c8r2030_closed
  · subst row; exact c8r2031_closed
theorem C8R02016G2 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2032_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r2032targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r2032choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2032targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] c8r2032choice = true := by decide
    refine ⟨c8r2032targets, c8r2032choice, ?_, checked⟩
    intro S h
    simp only [c8r2032targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 5 _ (by rfl)
  have c8r2033_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r2033targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r2033choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2033targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] c8r2033choice = true := by decide
    refine ⟨c8r2033targets, c8r2033choice, ?_, checked⟩
    intro S h
    simp only [c8r2033targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 7 _ (by rfl)
  have c8r2034_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c8r2034targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c8r2034choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2034targets [(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] c8r2034choice = true := by decide
    refine ⟨c8r2034targets, c8r2034choice, ?_, checked⟩
    intro S h
    simp only [c8r2034targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 15 _ (by rfl)
  have c8r2035_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c8r2035targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c8r2035choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,2),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2035targets [(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)] c8r2035choice = true := by decide
    refine ⟨c8r2035targets, c8r2035choice, ?_, checked⟩
    intro S h
    simp only [c8r2035targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 22 _ (by rfl)
  have c8r2036_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r2036targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r2036choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,2),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,-1),(10,(0,1))),((3,4),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2036targets [(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)] c8r2036choice = true := by decide
    refine ⟨c8r2036targets, c8r2036choice, ?_, checked⟩
    intro S h
    simp only [c8r2036targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,false] 30 _ (by rfl)
  have c8r2037_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r2037targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,5),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r2037choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((-1,5),(2,(1,0))),((0,0),(3,(0,0))),((0,1),(4,(0,0))),((0,3),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2037targets [(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r2037choice = true := by decide
    refine ⟨c8r2037targets, c8r2037choice, ?_, checked⟩
    intro S h
    simp only [c8r2037targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 8 _ (by rfl)
  have c8r2038_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r2038targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r2038choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,6),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2038targets [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r2038choice = true := by decide
    refine ⟨c8r2038targets, c8r2038choice, ?_, checked⟩
    intro S h
    simp only [c8r2038targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 17 _ (by rfl)
  have c8r2039_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c8r2039targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,3),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c8r2039choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2039targets [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c8r2039choice = true := by decide
    refine ⟨c8r2039targets, c8r2039choice, ?_, checked⟩
    intro S h
    simp only [c8r2039targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 22 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2032_closed
  · subst row; exact c8r2033_closed
  · subst row; exact c8r2034_closed
  · subst row; exact c8r2035_closed
  · subst row; exact c8r2036_closed
  · subst row; exact c8r2037_closed
  · subst row; exact c8r2038_closed
  · subst row; exact c8r2039_closed
theorem C8R02016G3 (row : List GridPoint) (h : row ∈ [[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r2040_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c8r2040targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c8r2040choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2040targets [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c8r2040choice = true := by decide
    refine ⟨c8r2040targets, c8r2040choice, ?_, checked⟩
    intro S h
    simp only [c8r2040targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 26 _ (by rfl)
  have c8r2041_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r2041targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r2041choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2041targets [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c8r2041choice = true := by decide
    refine ⟨c8r2041targets, c8r2041choice, ?_, checked⟩
    intro S h
    simp only [c8r2041targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 29 _ (by rfl)
  have c8r2042_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r2042targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r2042choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2042targets [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c8r2042choice = true := by decide
    refine ⟨c8r2042targets, c8r2042choice, ?_, checked⟩
    intro S h
    simp only [c8r2042targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 31 _ (by rfl)
  have c8r2043_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r2043targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r2043choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2043targets [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c8r2043choice = true := by decide
    refine ⟨c8r2043targets, c8r2043choice, ?_, checked⟩
    intro S h
    simp only [c8r2043targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 1 _ (by rfl)
  have c8r2044_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c8r2044targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,3),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c8r2044choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2044targets [(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c8r2044choice = true := by decide
    refine ⟨c8r2044targets, c8r2044choice, ?_, checked⟩
    intro S h
    simp only [c8r2044targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 9 _ (by rfl)
  have c8r2045_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c8r2045targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c8r2045choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2045targets [(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c8r2045choice = true := by decide
    refine ⟨c8r2045targets, c8r2045choice, ?_, checked⟩
    intro S h
    simp only [c8r2045targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 16 _ (by rfl)
  have c8r2046_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r2046targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r2046choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,5),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2046targets [(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c8r2046choice = true := by decide
    refine ⟨c8r2046targets, c8r2046choice, ?_, checked⟩
    intro S h
    simp only [c8r2046targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 27 _ (by rfl)
  have c8r2047_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c8r2047targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c8r2047choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((0,5),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,7),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r2047targets [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] c8r2047choice = true := by decide
    refine ⟨c8r2047targets, c8r2047choice, ?_, checked⟩
    intro S h
    simp only [c8r2047targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family9 [true,true,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [false,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,true,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family9 [true,true,false,false,true,true,true,false,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r2040_closed
  · subst row; exact c8r2041_closed
  · subst row; exact c8r2042_closed
  · subst row; exact c8r2043_closed
  · subst row; exact c8r2044_closed
  · subst row; exact c8r2045_closed
  · subst row; exact c8r2046_closed
  · subst row; exact c8r2047_closed
theorem C8R02016_closed (row : List GridPoint) (h : FamilyMember row F8B000L63) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L63, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R02016G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02016G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02016G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02016G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02016G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02016G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02016G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02016G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02016G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02016G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02016G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02016G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02016G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02016G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02016G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02016G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02016G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02016G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02016G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02016G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02016G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02016G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02016G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02016G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R02016G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R02016G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R02016G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R02016G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R02016G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R02016G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R02016G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R02016G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
