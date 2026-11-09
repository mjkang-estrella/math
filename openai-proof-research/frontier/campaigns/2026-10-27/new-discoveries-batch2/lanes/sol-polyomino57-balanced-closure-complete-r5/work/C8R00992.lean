import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00992G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r992_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)] := by
    let c8r992targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c8r992choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r992targets [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)] c8r992choice = true := by decide
    refine ⟨c8r992targets, c8r992choice, ?_, checked⟩
    intro S h
    simp only [c8r992targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 19 _ (by rfl)))
  have c8r993_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)] := by
    let c8r993targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c8r993choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r993targets [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)] c8r993choice = true := by decide
    refine ⟨c8r993targets, c8r993choice, ?_, checked⟩
    intro S h
    simp only [c8r993targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 21 _ (by rfl)))
  have c8r994_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)] := by
    let c8r994targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c8r994choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r994targets [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)] c8r994choice = true := by decide
    refine ⟨c8r994targets, c8r994choice, ?_, checked⟩
    intro S h
    simp only [c8r994targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 23 _ (by rfl)))
  have c8r995_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c8r995targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c8r995choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r995targets [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] c8r995choice = true := by decide
    refine ⟨c8r995targets, c8r995choice, ?_, checked⟩
    intro S h
    simp only [c8r995targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 26 _ (by rfl)))
  have c8r996_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)] := by
    let c8r996targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c8r996choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r996targets [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)] c8r996choice = true := by decide
    refine ⟨c8r996targets, c8r996choice, ?_, checked⟩
    intro S h
    simp only [c8r996targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 29 _ (by rfl)))
  have c8r997_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)] := by
    let c8r997targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c8r997choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r997targets [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)] c8r997choice = true := by decide
    refine ⟨c8r997targets, c8r997choice, ?_, checked⟩
    intro S h
    simp only [c8r997targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 0 _ (by rfl)))
  have c8r998_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] := by
    let c8r998targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c8r998choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,4),(10,(0,0))),((5,2),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r998targets [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)] c8r998choice = true := by decide
    refine ⟨c8r998targets, c8r998choice, ?_, checked⟩
    intro S h
    simp only [c8r998targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 3 _ (by rfl)))
  have c8r999_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] := by
    let c8r999targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c8r999choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,3),(12,(0,0))),((6,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r999targets [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)] c8r999choice = true := by decide
    refine ⟨c8r999targets, c8r999choice, ?_, checked⟩
    intro S h
    simp only [c8r999targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 6 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r992_closed
  · subst row; exact c8r993_closed
  · subst row; exact c8r994_closed
  · subst row; exact c8r995_closed
  · subst row; exact c8r996_closed
  · subst row; exact c8r997_closed
  · subst row; exact c8r998_closed
  · subst row; exact c8r999_closed
theorem C8R00992G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1000_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c8r1000targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c8r1000choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1000targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] c8r1000choice = true := by decide
    refine ⟨c8r1000targets, c8r1000choice, ?_, checked⟩
    intro S h
    simp only [c8r1000targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 11 _ (by rfl)))
  have c8r1001_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c8r1001targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c8r1001choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1001targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] c8r1001choice = true := by decide
    refine ⟨c8r1001targets, c8r1001choice, ?_, checked⟩
    intro S h
    simp only [c8r1001targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 13 _ (by rfl)))
  have c8r1002_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c8r1002targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c8r1002choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1002targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] c8r1002choice = true := by decide
    refine ⟨c8r1002targets, c8r1002choice, ?_, checked⟩
    intro S h
    simp only [c8r1002targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 15 _ (by rfl)))
  have c8r1003_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c8r1003targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c8r1003choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,4),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1003targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] c8r1003choice = true := by decide
    refine ⟨c8r1003targets, c8r1003choice, ?_, checked⟩
    intro S h
    simp only [c8r1003targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 19 _ (by rfl)))
  have c8r1004_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c8r1004targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c8r1004choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1004targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] c8r1004choice = true := by decide
    refine ⟨c8r1004targets, c8r1004choice, ?_, checked⟩
    intro S h
    simp only [c8r1004targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 22 _ (by rfl)))
  have c8r1005_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c8r1005targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c8r1005choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,3),(12,(0,0))),((6,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1005targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] c8r1005choice = true := by decide
    refine ⟨c8r1005targets, c8r1005choice, ?_, checked⟩
    intro S h
    simp only [c8r1005targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 24 _ (by rfl)))
  have c8r1006_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c8r1006targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c8r1006choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1006targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] c8r1006choice = true := by decide
    refine ⟨c8r1006targets, c8r1006choice, ?_, checked⟩
    intro S h
    simp only [c8r1006targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 27 _ (by rfl)))
  have c8r1007_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c8r1007targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c8r1007choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,3),(12,(0,0))),((6,1),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1007targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)] c8r1007choice = true := by decide
    refine ⟨c8r1007targets, c8r1007choice, ?_, checked⟩
    intro S h
    simp only [c8r1007targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 30 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1000_closed
  · subst row; exact c8r1001_closed
  · subst row; exact c8r1002_closed
  · subst row; exact c8r1003_closed
  · subst row; exact c8r1004_closed
  · subst row; exact c8r1005_closed
  · subst row; exact c8r1006_closed
  · subst row; exact c8r1007_closed
theorem C8R00992G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1008_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c8r1008targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c8r1008choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,2),(14,(0,0))),((7,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1008targets [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)] c8r1008choice = true := by decide
    refine ⟨c8r1008targets, c8r1008choice, ?_, checked⟩
    intro S h
    simp only [c8r1008targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L29_lift _ (familyLookup_sound F9B001L29 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L34_lift _ (familyLookup_sound F9B001L34 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 1 _ (by rfl)))
  have c8r1009_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c8r1009targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c8r1009choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0))),((3,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1009targets [(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c8r1009choice = true := by decide
    refine ⟨c8r1009targets, c8r1009choice, ?_, checked⟩
    intro S h
    simp only [c8r1009targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L18_lift _ (familyLookup_sound F9B001L18 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 7 _ (by rfl)))
  have c8r1010_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c8r1010targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c8r1010choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1010targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c8r1010choice = true := by decide
    refine ⟨c8r1010targets, c8r1010choice, ?_, checked⟩
    intro S h
    simp only [c8r1010targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 12 _ (by rfl)))
  have c8r1011_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c8r1011targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c8r1011choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1011targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c8r1011choice = true := by decide
    refine ⟨c8r1011targets, c8r1011choice, ?_, checked⟩
    intro S h
    simp only [c8r1011targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 15 _ (by rfl)))
  have c8r1012_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] := by
    let c8r1012targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c8r1012choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1012targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] c8r1012choice = true := by decide
    refine ⟨c8r1012targets, c8r1012choice, ?_, checked⟩
    intro S h
    simp only [c8r1012targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 17 _ (by rfl)))
  have c8r1013_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] := by
    let c8r1013targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c8r1013choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1013targets [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] c8r1013choice = true := by decide
    refine ⟨c8r1013targets, c8r1013choice, ?_, checked⟩
    intro S h
    simp only [c8r1013targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L17_lift _ (familyLookup_sound F9B001L17 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L21_lift _ (familyLookup_sound F9B001L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 19 _ (by rfl)))
  have c8r1014_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c8r1014targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c8r1014choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1014targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] c8r1014choice = true := by decide
    refine ⟨c8r1014targets, c8r1014choice, ?_, checked⟩
    intro S h
    simp only [c8r1014targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 27 _ (by rfl)))
  have c8r1015_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c8r1015targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c8r1015choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1015targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] c8r1015choice = true := by decide
    refine ⟨c8r1015targets, c8r1015choice, ?_, checked⟩
    intro S h
    simp only [c8r1015targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 31 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1008_closed
  · subst row; exact c8r1009_closed
  · subst row; exact c8r1010_closed
  · subst row; exact c8r1011_closed
  · subst row; exact c8r1012_closed
  · subst row; exact c8r1013_closed
  · subst row; exact c8r1014_closed
  · subst row; exact c8r1015_closed
theorem C8R00992G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r1016_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r1016targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r1016choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1016targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] c8r1016choice = true := by decide
    refine ⟨c8r1016targets, c8r1016choice, ?_, checked⟩
    intro S h
    simp only [c8r1016targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 2 _ (by rfl)))
  have c8r1017_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r1017targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r1017choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1017targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] c8r1017choice = true := by decide
    refine ⟨c8r1017targets, c8r1017choice, ?_, checked⟩
    intro S h
    simp only [c8r1017targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 4 _ (by rfl)))
  have c8r1018_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r1018targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r1018choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1018targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] c8r1018choice = true := by decide
    refine ⟨c8r1018targets, c8r1018choice, ?_, checked⟩
    intro S h
    simp only [c8r1018targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 6 _ (by rfl)))
  have c8r1019_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r1019targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r1019choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1019targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] c8r1019choice = true := by decide
    refine ⟨c8r1019targets, c8r1019choice, ?_, checked⟩
    intro S h
    simp only [c8r1019targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 9 _ (by rfl)))
  have c8r1020_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c8r1020targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c8r1020choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1020targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] c8r1020choice = true := by decide
    refine ⟨c8r1020targets, c8r1020choice, ?_, checked⟩
    intro S h
    simp only [c8r1020targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 12 _ (by rfl)))
  have c8r1021_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c8r1021targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c8r1021choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1021targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] c8r1021choice = true := by decide
    refine ⟨c8r1021targets, c8r1021choice, ?_, checked⟩
    intro S h
    simp only [c8r1021targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 14 _ (by rfl)))
  have c8r1022_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r1022targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r1022choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1022targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] c8r1022choice = true := by decide
    refine ⟨c8r1022targets, c8r1022choice, ?_, checked⟩
    intro S h
    simp only [c8r1022targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 17 _ (by rfl)))
  have c8r1023_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r1023targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r1023choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r1023targets [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] c8r1023choice = true := by decide
    refine ⟨c8r1023targets, c8r1023choice, ?_, checked⟩
    intro S h
    simp only [c8r1023targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L51_lift _ (familyLookup_sound F9B001L51 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L50_lift _ (familyLookup_sound F9B000L50 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L14_lift _ (familyLookup_sound F9B001L14 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L39_lift _ (familyLookup_sound F9B002L39 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L41_lift _ (familyLookup_sound F9B001L41 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L58_lift _ (familyLookup_sound F9B002L58 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L42_lift _ (familyLookup_sound F9B001L42 [] 20 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r1016_closed
  · subst row; exact c8r1017_closed
  · subst row; exact c8r1018_closed
  · subst row; exact c8r1019_closed
  · subst row; exact c8r1020_closed
  · subst row; exact c8r1021_closed
  · subst row; exact c8r1022_closed
  · subst row; exact c8r1023_closed
theorem C8R00992_closed (row : List GridPoint) (h : FamilyMember row F8B000L31) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L31, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00992G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00992G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00992G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00992G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00992G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00992G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00992G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00992G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00992G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00992G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00992G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00992G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00992G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00992G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00992G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00992G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00992G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00992G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00992G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00992G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00992G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00992G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00992G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00992G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00992G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00992G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00992G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00992G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00992G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00992G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00992G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00992G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
