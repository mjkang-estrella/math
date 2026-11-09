import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00864G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r864_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)] := by
    let c8r864targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0)]]
    let c8r864choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r864targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)] c8r864choice = true := by decide
    refine ⟨c8r864targets, c8r864choice, ?_, checked⟩
    intro S h
    simp only [c8r864targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 23 _ (by rfl)))
  have c8r865_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)] := by
    let c8r865targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)]]
    let c8r865choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r865targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)] c8r865choice = true := by decide
    refine ⟨c8r865targets, c8r865choice, ?_, checked⟩
    intro S h
    simp only [c8r865targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 26 _ (by rfl)))
  have c8r866_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)] := by
    let c8r866targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,3)]]
    let c8r866choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r866targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)] c8r866choice = true := by decide
    refine ⟨c8r866targets, c8r866choice, ?_, checked⟩
    intro S h
    simp only [c8r866targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 29 _ (by rfl)))
  have c8r867_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)] := by
    let c8r867targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2),(4,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2),(5,2)]]
    let c8r867choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r867targets [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)] c8r867choice = true := by decide
    refine ⟨c8r867targets, c8r867choice, ?_, checked⟩
    intro S h
    simp only [c8r867targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L50_lift _ (familyLookup_sound F9B002L50 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 0 _ (by rfl)))
  have c8r868_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)] := by
    let c8r868targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)]]
    let c8r868choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r868targets [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)] c8r868choice = true := by decide
    refine ⟨c8r868targets, c8r868choice, ?_, checked⟩
    intro S h
    simp only [c8r868targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 4 _ (by rfl)))
  have c8r869_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)] := by
    let c8r869targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)]]
    let c8r869choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r869targets [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)] c8r869choice = true := by decide
    refine ⟨c8r869targets, c8r869choice, ?_, checked⟩
    intro S h
    simp only [c8r869targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 6 _ (by rfl)))
  have c8r870_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)] := by
    let c8r870targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)]]
    let c8r870choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r870targets [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)] c8r870choice = true := by decide
    refine ⟨c8r870targets, c8r870choice, ?_, checked⟩
    intro S h
    simp only [c8r870targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 8 _ (by rfl)))
  have c8r871_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)] := by
    let c8r871targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)]]
    let c8r871choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,2),(12,(0,0))),((5,0),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r871targets [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)] c8r871choice = true := by decide
    refine ⟨c8r871targets, c8r871choice, ?_, checked⟩
    intro S h
    simp only [c8r871targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 11 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r864_closed
  · subst row; exact c8r865_closed
  · subst row; exact c8r866_closed
  · subst row; exact c8r867_closed
  · subst row; exact c8r868_closed
  · subst row; exact c8r869_closed
  · subst row; exact c8r870_closed
  · subst row; exact c8r871_closed
theorem C8R00864G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r872_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)] := by
    let c8r872targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)]]
    let c8r872choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,-1),(13,(0,1))),((5,1),(14,(0,0))),((6,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r872targets [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)] c8r872choice = true := by decide
    refine ⟨c8r872targets, c8r872choice, ?_, checked⟩
    intro S h
    simp only [c8r872targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L12_lift _ (familyLookup_sound F9B001L12 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L22_lift _ (familyLookup_sound F9B001L22 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 13 _ (by rfl)))
  have c8r873_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r873targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r873choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r873targets [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)] c8r873choice = true := by decide
    refine ⟨c8r873targets, c8r873choice, ?_, checked⟩
    intro S h
    simp only [c8r873targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 18 _ (by rfl)))
  have c8r874_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r874targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r874choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r874targets [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)] c8r874choice = true := by decide
    refine ⟨c8r874targets, c8r874choice, ?_, checked⟩
    intro S h
    simp only [c8r874targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 22 _ (by rfl)))
  have c8r875_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r875targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r875choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r875targets [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)] c8r875choice = true := by decide
    refine ⟨c8r875targets, c8r875choice, ?_, checked⟩
    intro S h
    simp only [c8r875targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 24 _ (by rfl)))
  have c8r876_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r876targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r876choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r876targets [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)] c8r876choice = true := by decide
    refine ⟨c8r876targets, c8r876choice, ?_, checked⟩
    intro S h
    simp only [c8r876targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 26 _ (by rfl)))
  have c8r877_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r877targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r877choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r877targets [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)] c8r877choice = true := by decide
    refine ⟨c8r877targets, c8r877choice, ?_, checked⟩
    intro S h
    simp only [c8r877targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L31_lift _ (familyLookup_sound F9B002L31 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L51_lift _ (familyLookup_sound F9B002L51 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 29 _ (by rfl)))
  have c8r878_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r878targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r878choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r878targets [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)] c8r878choice = true := by decide
    refine ⟨c8r878targets, c8r878choice, ?_, checked⟩
    intro S h
    simp only [c8r878targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 0 _ (by rfl)))
  have c8r879_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r879targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r879choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r879targets [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)] c8r879choice = true := by decide
    refine ⟨c8r879targets, c8r879choice, ?_, checked⟩
    intro S h
    simp only [c8r879targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 3 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r872_closed
  · subst row; exact c8r873_closed
  · subst row; exact c8r874_closed
  · subst row; exact c8r875_closed
  · subst row; exact c8r876_closed
  · subst row; exact c8r877_closed
  · subst row; exact c8r878_closed
  · subst row; exact c8r879_closed
theorem C8R00864G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r880_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r880targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r880choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r880targets [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)] c8r880choice = true := by decide
    refine ⟨c8r880targets, c8r880choice, ?_, checked⟩
    intro S h
    simp only [c8r880targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 6 _ (by rfl)))
  have c8r881_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r881targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r881choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r881targets [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)] c8r881choice = true := by decide
    refine ⟨c8r881targets, c8r881choice, ?_, checked⟩
    intro S h
    simp only [c8r881targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 9 _ (by rfl)))
  have c8r882_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r882targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r882choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r882targets [(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)] c8r882choice = true := by decide
    refine ⟨c8r882targets, c8r882choice, ?_, checked⟩
    intro S h
    simp only [c8r882targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 14 _ (by rfl)))
  have c8r883_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r883targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r883choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r883targets [(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)] c8r883choice = true := by decide
    refine ⟨c8r883targets, c8r883choice, ?_, checked⟩
    intro S h
    simp only [c8r883targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 16 _ (by rfl)))
  have c8r884_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r884targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r884choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r884targets [(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)] c8r884choice = true := by decide
    refine ⟨c8r884targets, c8r884choice, ?_, checked⟩
    intro S h
    simp only [c8r884targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 18 _ (by rfl)))
  have c8r885_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)] := by
    let c8r885targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c8r885choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r885targets [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)] c8r885choice = true := by decide
    refine ⟨c8r885targets, c8r885choice, ?_, checked⟩
    intro S h
    simp only [c8r885targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 22 _ (by rfl)))
  have c8r886_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)] := by
    let c8r886targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c8r886choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r886targets [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)] c8r886choice = true := by decide
    refine ⟨c8r886targets, c8r886choice, ?_, checked⟩
    intro S h
    simp only [c8r886targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L46_lift _ (familyLookup_sound F9B001L46 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 25 _ (by rfl)))
  have c8r887_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)] := by
    let c8r887targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c8r887choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r887targets [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)] c8r887choice = true := by decide
    refine ⟨c8r887targets, c8r887choice, ?_, checked⟩
    intro S h
    simp only [c8r887targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 27 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r880_closed
  · subst row; exact c8r881_closed
  · subst row; exact c8r882_closed
  · subst row; exact c8r883_closed
  · subst row; exact c8r884_closed
  · subst row; exact c8r885_closed
  · subst row; exact c8r886_closed
  · subst row; exact c8r887_closed
theorem C8R00864G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r888_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r888targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r888choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r888targets [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)] c8r888choice = true := by decide
    refine ⟨c8r888targets, c8r888choice, ?_, checked⟩
    intro S h
    simp only [c8r888targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L52_lift _ (familyLookup_sound F9B002L52 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 30 _ (by rfl)))
  have c8r889_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)] := by
    let c8r889targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c8r889choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r889targets [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)] c8r889choice = true := by decide
    refine ⟨c8r889targets, c8r889choice, ?_, checked⟩
    intro S h
    simp only [c8r889targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 1 _ (by rfl)))
  have c8r890_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)] := by
    let c8r890targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c8r890choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r890targets [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)] c8r890choice = true := by decide
    refine ⟨c8r890targets, c8r890choice, ?_, checked⟩
    intro S h
    simp only [c8r890targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 4 _ (by rfl)))
  have c8r891_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)] := by
    let c8r891targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c8r891choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,6),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r891targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)] c8r891choice = true := by decide
    refine ⟨c8r891targets, c8r891choice, ?_, checked⟩
    intro S h
    simp only [c8r891targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 9 _ (by rfl)))
  have c8r892_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)] := by
    let c8r892targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c8r892choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r892targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)] c8r892choice = true := by decide
    refine ⟨c8r892targets, c8r892choice, ?_, checked⟩
    intro S h
    simp only [c8r892targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 13 _ (by rfl)))
  have c8r893_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)] := by
    let c8r893targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c8r893choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r893targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)] c8r893choice = true := by decide
    refine ⟨c8r893targets, c8r893choice, ?_, checked⟩
    intro S h
    simp only [c8r893targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L23_lift _ (familyLookup_sound F9B001L23 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 15 _ (by rfl)))
  have c8r894_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)] := by
    let c8r894targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c8r894choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,5),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r894targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)] c8r894choice = true := by decide
    refine ⟨c8r894targets, c8r894choice, ?_, checked⟩
    intro S h
    simp only [c8r894targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 17 _ (by rfl)))
  have c8r895_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)] := by
    let c8r895targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c8r895choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r895targets [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)] c8r895choice = true := by decide
    refine ⟨c8r895targets, c8r895choice, ?_, checked⟩
    intro S h
    simp only [c8r895targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L47_lift _ (familyLookup_sound F9B001L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L13_lift _ (familyLookup_sound F9B001L13 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 21 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r888_closed
  · subst row; exact c8r889_closed
  · subst row; exact c8r890_closed
  · subst row; exact c8r891_closed
  · subst row; exact c8r892_closed
  · subst row; exact c8r893_closed
  · subst row; exact c8r894_closed
  · subst row; exact c8r895_closed
theorem C8R00864_closed (row : List GridPoint) (h : FamilyMember row F8B000L27) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L27, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00864G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00864G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00864G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00864G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00864G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00864G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00864G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00864G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00864G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00864G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00864G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00864G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00864G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00864G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00864G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00864G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00864G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00864G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00864G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00864G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00864G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00864G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00864G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00864G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00864G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00864G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00864G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00864G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00864G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00864G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00864G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00864G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
