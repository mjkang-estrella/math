import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00608G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r608_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)] := by
    let c8r608targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c8r608choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,4),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r608targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)] c8r608choice = true := by decide
    refine ⟨c8r608targets, c8r608choice, ?_, checked⟩
    intro S h
    simp only [c8r608targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 4 _ (by rfl)))
  have c8r609_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)] := by
    let c8r609targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c8r609choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r609targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)] c8r609choice = true := by decide
    refine ⟨c8r609targets, c8r609choice, ?_, checked⟩
    intro S h
    simp only [c8r609targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 8 _ (by rfl)))
  have c8r610_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)] := by
    let c8r610targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c8r610choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r610targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)] c8r610choice = true := by decide
    refine ⟨c8r610targets, c8r610choice, ?_, checked⟩
    intro S h
    simp only [c8r610targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 11 _ (by rfl)))
  have c8r611_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)] := by
    let c8r611targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c8r611choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r611targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)] c8r611choice = true := by decide
    refine ⟨c8r611targets, c8r611choice, ?_, checked⟩
    intro S h
    simp only [c8r611targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 14 _ (by rfl)))
  have c8r612_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] := by
    let c8r612targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)]]
    let c8r612choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r612targets [(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)] c8r612choice = true := by decide
    refine ⟨c8r612targets, c8r612choice, ?_, checked⟩
    intro S h
    simp only [c8r612targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L55_lift _ (familyLookup_sound F9B000L55 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 20 _ (by rfl)))
  have c8r613_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r613targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r613choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r613targets [(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r613choice = true := by decide
    refine ⟨c8r613targets, c8r613choice, ?_, checked⟩
    intro S h
    simp only [c8r613targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 25 _ (by rfl)))
  have c8r614_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r614targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r614choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r614targets [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)] c8r614choice = true := by decide
    refine ⟨c8r614targets, c8r614choice, ?_, checked⟩
    intro S h
    simp only [c8r614targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 30 _ (by rfl)))
  have c8r615_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r615targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r615choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r615targets [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)] c8r615choice = true := by decide
    refine ⟨c8r615targets, c8r615choice, ?_, checked⟩
    intro S h
    simp only [c8r615targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 2 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r608_closed
  · subst row; exact c8r609_closed
  · subst row; exact c8r610_closed
  · subst row; exact c8r611_closed
  · subst row; exact c8r612_closed
  · subst row; exact c8r613_closed
  · subst row; exact c8r614_closed
  · subst row; exact c8r615_closed
theorem C8R00608G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r616_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r616targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r616choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r616targets [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)] c8r616choice = true := by decide
    refine ⟨c8r616targets, c8r616choice, ?_, checked⟩
    intro S h
    simp only [c8r616targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 4 _ (by rfl)))
  have c8r617_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r617targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r617choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r617targets [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)] c8r617choice = true := by decide
    refine ⟨c8r617targets, c8r617choice, ?_, checked⟩
    intro S h
    simp only [c8r617targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L41_lift _ (familyLookup_sound F9B000L41 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 6 _ (by rfl)))
  have c8r618_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r618targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r618choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,5),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r618targets [(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)] c8r618choice = true := by decide
    refine ⟨c8r618targets, c8r618choice, ?_, checked⟩
    intro S h
    simp only [c8r618targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L43_lift _ (familyLookup_sound F9B000L43 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 14 _ (by rfl)))
  have c8r619_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r619targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r619choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r619targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r619choice = true := by decide
    refine ⟨c8r619targets, c8r619choice, ?_, checked⟩
    intro S h
    simp only [c8r619targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 21 _ (by rfl)))
  have c8r620_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c8r620targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c8r620choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r620targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)] c8r620choice = true := by decide
    refine ⟨c8r620targets, c8r620choice, ?_, checked⟩
    intro S h
    simp only [c8r620targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 25 _ (by rfl)))
  have c8r621_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r621targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r621choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r621targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)] c8r621choice = true := by decide
    refine ⟨c8r621targets, c8r621choice, ?_, checked⟩
    intro S h
    simp only [c8r621targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 28 _ (by rfl)))
  have c8r622_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r622targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r622choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r622targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)] c8r622choice = true := by decide
    refine ⟨c8r622targets, c8r622choice, ?_, checked⟩
    intro S h
    simp only [c8r622targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 30 _ (by rfl)))
  have c8r623_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r623targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r623choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r623targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)] c8r623choice = true := by decide
    refine ⟨c8r623targets, c8r623choice, ?_, checked⟩
    intro S h
    simp only [c8r623targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 0 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r616_closed
  · subst row; exact c8r617_closed
  · subst row; exact c8r618_closed
  · subst row; exact c8r619_closed
  · subst row; exact c8r620_closed
  · subst row; exact c8r621_closed
  · subst row; exact c8r622_closed
  · subst row; exact c8r623_closed
theorem C8R00608G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r624_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r624targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r624choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r624targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)] c8r624choice = true := by decide
    refine ⟨c8r624targets, c8r624choice, ?_, checked⟩
    intro S h
    simp only [c8r624targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 3 _ (by rfl)))
  have c8r625_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c8r625targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c8r625choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r625targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)] c8r625choice = true := by decide
    refine ⟨c8r625targets, c8r625choice, ?_, checked⟩
    intro S h
    simp only [c8r625targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 6 _ (by rfl)))
  have c8r626_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c8r626targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c8r626choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r626targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)] c8r626choice = true := by decide
    refine ⟨c8r626targets, c8r626choice, ?_, checked⟩
    intro S h
    simp only [c8r626targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 8 _ (by rfl)))
  have c8r627_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r627targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r627choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r627targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)] c8r627choice = true := by decide
    refine ⟨c8r627targets, c8r627choice, ?_, checked⟩
    intro S h
    simp only [c8r627targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 11 _ (by rfl)))
  have c8r628_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r628targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r628choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r628targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)] c8r628choice = true := by decide
    refine ⟨c8r628targets, c8r628choice, ?_, checked⟩
    intro S h
    simp only [c8r628targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 14 _ (by rfl)))
  have c8r629_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r629targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r629choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r629targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)] c8r629choice = true := by decide
    refine ⟨c8r629targets, c8r629choice, ?_, checked⟩
    intro S h
    simp only [c8r629targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 17 _ (by rfl)))
  have c8r630_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r630targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r630choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r630targets [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)] c8r630choice = true := by decide
    refine ⟨c8r630targets, c8r630choice, ?_, checked⟩
    intro S h
    simp only [c8r630targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 20 _ (by rfl)))
  have c8r631_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r631targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r631choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r631targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] c8r631choice = true := by decide
    refine ⟨c8r631targets, c8r631choice, ?_, checked⟩
    intro S h
    simp only [c8r631targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 25 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r624_closed
  · subst row; exact c8r625_closed
  · subst row; exact c8r626_closed
  · subst row; exact c8r627_closed
  · subst row; exact c8r628_closed
  · subst row; exact c8r629_closed
  · subst row; exact c8r630_closed
  · subst row; exact c8r631_closed
theorem C8R00608G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r632_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r632targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r632choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r632targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] c8r632choice = true := by decide
    refine ⟨c8r632targets, c8r632choice, ?_, checked⟩
    intro S h
    simp only [c8r632targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 27 _ (by rfl)))
  have c8r633_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r633targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r633choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r633targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] c8r633choice = true := by decide
    refine ⟨c8r633targets, c8r633choice, ?_, checked⟩
    intro S h
    simp only [c8r633targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 29 _ (by rfl)))
  have c8r634_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] := by
    let c8r634targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
    let c8r634choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r634targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] c8r634choice = true := by decide
    refine ⟨c8r634targets, c8r634choice, ?_, checked⟩
    intro S h
    simp only [c8r634targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 0 _ (by rfl)))
  have c8r635_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] := by
    let c8r635targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
    let c8r635choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r635targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] c8r635choice = true := by decide
    refine ⟨c8r635targets, c8r635choice, ?_, checked⟩
    intro S h
    simp only [c8r635targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 2 _ (by rfl)))
  have c8r636_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] := by
    let c8r636targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c8r636choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r636targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] c8r636choice = true := by decide
    refine ⟨c8r636targets, c8r636choice, ?_, checked⟩
    intro S h
    simp only [c8r636targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 6 _ (by rfl)))
  have c8r637_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] := by
    let c8r637targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c8r637choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r637targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] c8r637choice = true := by decide
    refine ⟨c8r637targets, c8r637choice, ?_, checked⟩
    intro S h
    simp only [c8r637targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 9 _ (by rfl)))
  have c8r638_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] := by
    let c8r638targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c8r638choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r638targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] c8r638choice = true := by decide
    refine ⟨c8r638targets, c8r638choice, ?_, checked⟩
    intro S h
    simp only [c8r638targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 11 _ (by rfl)))
  have c8r639_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r639targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r639choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r639targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] c8r639choice = true := by decide
    refine ⟨c8r639targets, c8r639choice, ?_, checked⟩
    intro S h
    simp only [c8r639targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L36_lift _ (familyLookup_sound F9B000L36 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 14 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r632_closed
  · subst row; exact c8r633_closed
  · subst row; exact c8r634_closed
  · subst row; exact c8r635_closed
  · subst row; exact c8r636_closed
  · subst row; exact c8r637_closed
  · subst row; exact c8r638_closed
  · subst row; exact c8r639_closed
theorem C8R00608_closed (row : List GridPoint) (h : FamilyMember row F8B000L19) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L19, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00608G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00608G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00608G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00608G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00608G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00608G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00608G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00608G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00608G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00608G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00608G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00608G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00608G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00608G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00608G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00608G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00608G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00608G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00608G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00608G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00608G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00608G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00608G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00608G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00608G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00608G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00608G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00608G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00608G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00608G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00608G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00608G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
