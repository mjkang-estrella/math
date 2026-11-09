import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00576G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r576_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)] := by
    let c8r576targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c8r576choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r576targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)] c8r576choice = true := by decide
    refine ⟨c8r576targets, c8r576choice, ?_, checked⟩
    intro S h
    simp only [c8r576targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 2 _ (by rfl)))
  have c8r577_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)] := by
    let c8r577targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c8r577choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r577targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)] c8r577choice = true := by decide
    refine ⟨c8r577targets, c8r577choice, ?_, checked⟩
    intro S h
    simp only [c8r577targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 4 _ (by rfl)))
  have c8r578_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)] := by
    let c8r578targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c8r578choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r578targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)] c8r578choice = true := by decide
    refine ⟨c8r578targets, c8r578choice, ?_, checked⟩
    intro S h
    simp only [c8r578targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 6 _ (by rfl)))
  have c8r579_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)] := by
    let c8r579targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c8r579choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r579targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)] c8r579choice = true := by decide
    refine ⟨c8r579targets, c8r579choice, ?_, checked⟩
    intro S h
    simp only [c8r579targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L45_lift _ (familyLookup_sound F9B000L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 9 _ (by rfl)))
  have c8r580_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)] := by
    let c8r580targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c8r580choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r580targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)] c8r580choice = true := by decide
    refine ⟨c8r580targets, c8r580choice, ?_, checked⟩
    intro S h
    simp only [c8r580targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 12 _ (by rfl)))
  have c8r581_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)] := by
    let c8r581targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c8r581choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r581targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)] c8r581choice = true := by decide
    refine ⟨c8r581targets, c8r581choice, ?_, checked⟩
    intro S h
    simp only [c8r581targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 15 _ (by rfl)))
  have c8r582_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)] := by
    let c8r582targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c8r582choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r582targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)] c8r582choice = true := by decide
    refine ⟨c8r582targets, c8r582choice, ?_, checked⟩
    intro S h
    simp only [c8r582targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L28_lift _ (familyLookup_sound F9B000L28 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L56_lift _ (familyLookup_sound F9B000L56 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 18 _ (by rfl)))
  have c8r583_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)] := by
    let c8r583targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c8r583choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r583targets [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)] c8r583choice = true := by decide
    refine ⟨c8r583targets, c8r583choice, ?_, checked⟩
    intro S h
    simp only [c8r583targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 21 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r576_closed
  · subst row; exact c8r577_closed
  · subst row; exact c8r578_closed
  · subst row; exact c8r579_closed
  · subst row; exact c8r580_closed
  · subst row; exact c8r581_closed
  · subst row; exact c8r582_closed
  · subst row; exact c8r583_closed
theorem C8R00576G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r584_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)] := by
    let c8r584targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c8r584choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r584targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)] c8r584choice = true := by decide
    refine ⟨c8r584targets, c8r584choice, ?_, checked⟩
    intro S h
    simp only [c8r584targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 26 _ (by rfl)))
  have c8r585_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)] := by
    let c8r585targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c8r585choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r585targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)] c8r585choice = true := by decide
    refine ⟨c8r585targets, c8r585choice, ?_, checked⟩
    intro S h
    simp only [c8r585targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 28 _ (by rfl)))
  have c8r586_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)] := by
    let c8r586targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c8r586choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r586targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)] c8r586choice = true := by decide
    refine ⟨c8r586targets, c8r586choice, ?_, checked⟩
    intro S h
    simp only [c8r586targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 30 _ (by rfl)))
  have c8r587_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)] := by
    let c8r587targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c8r587choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r587targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)] c8r587choice = true := by decide
    refine ⟨c8r587targets, c8r587choice, ?_, checked⟩
    intro S h
    simp only [c8r587targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 2 _ (by rfl)))
  have c8r588_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)] := by
    let c8r588targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c8r588choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r588targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)] c8r588choice = true := by decide
    refine ⟨c8r588targets, c8r588choice, ?_, checked⟩
    intro S h
    simp only [c8r588targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 5 _ (by rfl)))
  have c8r589_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)] := by
    let c8r589targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c8r589choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r589targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)] c8r589choice = true := by decide
    refine ⟨c8r589targets, c8r589choice, ?_, checked⟩
    intro S h
    simp only [c8r589targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 7 _ (by rfl)))
  have c8r590_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)] := by
    let c8r590targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c8r590choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r590targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)] c8r590choice = true := by decide
    refine ⟨c8r590targets, c8r590choice, ?_, checked⟩
    intro S h
    simp only [c8r590targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 10 _ (by rfl)))
  have c8r591_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)] := by
    let c8r591targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c8r591choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r591targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)] c8r591choice = true := by decide
    refine ⟨c8r591targets, c8r591choice, ?_, checked⟩
    intro S h
    simp only [c8r591targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 13 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r584_closed
  · subst row; exact c8r585_closed
  · subst row; exact c8r586_closed
  · subst row; exact c8r587_closed
  · subst row; exact c8r588_closed
  · subst row; exact c8r589_closed
  · subst row; exact c8r590_closed
  · subst row; exact c8r591_closed
theorem C8R00576G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r592_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)] := by
    let c8r592targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c8r592choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r592targets [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)] c8r592choice = true := by decide
    refine ⟨c8r592targets, c8r592choice, ?_, checked⟩
    intro S h
    simp only [c8r592targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 16 _ (by rfl)))
  have c8r593_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)] := by
    let c8r593targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c8r593choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,6),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((3,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r593targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)] c8r593choice = true := by decide
    refine ⟨c8r593targets, c8r593choice, ?_, checked⟩
    intro S h
    simp only [c8r593targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L34_lift _ (familyLookup_sound F9B000L34 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 21 _ (by rfl)))
  have c8r594_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)] := by
    let c8r594targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c8r594choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r594targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)] c8r594choice = true := by decide
    refine ⟨c8r594targets, c8r594choice, ?_, checked⟩
    intro S h
    simp only [c8r594targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 25 _ (by rfl)))
  have c8r595_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)] := by
    let c8r595targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c8r595choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r595targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)] c8r595choice = true := by decide
    refine ⟨c8r595targets, c8r595choice, ?_, checked⟩
    intro S h
    simp only [c8r595targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 27 _ (by rfl)))
  have c8r596_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)] := by
    let c8r596targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c8r596choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((3,5),(11,(0,0))),((4,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r596targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)] c8r596choice = true := by decide
    refine ⟨c8r596targets, c8r596choice, ?_, checked⟩
    intro S h
    simp only [c8r596targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 29 _ (by rfl)))
  have c8r597_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)] := by
    let c8r597targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c8r597choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r597targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)] c8r597choice = true := by decide
    refine ⟨c8r597targets, c8r597choice, ?_, checked⟩
    intro S h
    simp only [c8r597targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 1 _ (by rfl)))
  have c8r598_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)] := by
    let c8r598targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c8r598choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r598targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)] c8r598choice = true := by decide
    refine ⟨c8r598targets, c8r598choice, ?_, checked⟩
    intro S h
    simp only [c8r598targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 4 _ (by rfl)))
  have c8r599_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)] := by
    let c8r599targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c8r599choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r599targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)] c8r599choice = true := by decide
    refine ⟨c8r599targets, c8r599choice, ?_, checked⟩
    intro S h
    simp only [c8r599targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 7 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r592_closed
  · subst row; exact c8r593_closed
  · subst row; exact c8r594_closed
  · subst row; exact c8r595_closed
  · subst row; exact c8r596_closed
  · subst row; exact c8r597_closed
  · subst row; exact c8r598_closed
  · subst row; exact c8r599_closed
theorem C8R00576G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r600_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)] := by
    let c8r600targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c8r600choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,2),(8,(0,0))),((3,5),(9,(0,0))),((4,3),(10,(0,0))),((4,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r600targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)] c8r600choice = true := by decide
    refine ⟨c8r600targets, c8r600choice, ?_, checked⟩
    intro S h
    simp only [c8r600targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L45_lift _ (familyLookup_sound F9B002L45 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 10 _ (by rfl)))
  have c8r601_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)] := by
    let c8r601targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c8r601choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,2),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,4),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r601targets [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)] c8r601choice = true := by decide
    refine ⟨c8r601targets, c8r601choice, ?_, checked⟩
    intro S h
    simp only [c8r601targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 13 _ (by rfl)))
  have c8r602_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r602targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r602choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r602targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)] c8r602choice = true := by decide
    refine ⟨c8r602targets, c8r602choice, ?_, checked⟩
    intro S h
    simp only [c8r602targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L18_lift _ (familyLookup_sound F9B002L18 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 18 _ (by rfl)))
  have c8r603_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)] := by
    let c8r603targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c8r603choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r603targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)] c8r603choice = true := by decide
    refine ⟨c8r603targets, c8r603choice, ?_, checked⟩
    intro S h
    simp only [c8r603targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L57_lift _ (familyLookup_sound F9B000L57 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 22 _ (by rfl)))
  have c8r604_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)] := by
    let c8r604targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c8r604choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r604targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)] c8r604choice = true := by decide
    refine ⟨c8r604targets, c8r604choice, ?_, checked⟩
    intro S h
    simp only [c8r604targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 25 _ (by rfl)))
  have c8r605_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)] := by
    let c8r605targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c8r605choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r605targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)] c8r605choice = true := by decide
    refine ⟨c8r605targets, c8r605choice, ?_, checked⟩
    intro S h
    simp only [c8r605targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 27 _ (by rfl)))
  have c8r606_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)] := by
    let c8r606targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c8r606choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r606targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)] c8r606choice = true := by decide
    refine ⟨c8r606targets, c8r606choice, ?_, checked⟩
    intro S h
    simp only [c8r606targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 31 _ (by rfl)))
  have c8r607_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)] := by
    let c8r607targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c8r607choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r607targets [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)] c8r607choice = true := by decide
    refine ⟨c8r607targets, c8r607choice, ?_, checked⟩
    intro S h
    simp only [c8r607targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L46_lift _ (familyLookup_sound F9B002L46 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L35_lift _ (familyLookup_sound F9B000L35 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L29_lift _ (familyLookup_sound F9B000L29 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L46_lift _ (familyLookup_sound F9B000L46 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L58_lift _ (familyLookup_sound F9B000L58 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 2 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r600_closed
  · subst row; exact c8r601_closed
  · subst row; exact c8r602_closed
  · subst row; exact c8r603_closed
  · subst row; exact c8r604_closed
  · subst row; exact c8r605_closed
  · subst row; exact c8r606_closed
  · subst row; exact c8r607_closed
theorem C8R00576_closed (row : List GridPoint) (h : FamilyMember row F8B000L18) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L18, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00576G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00576G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00576G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00576G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00576G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00576G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00576G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00576G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00576G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00576G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00576G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00576G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00576G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00576G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00576G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00576G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00576G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00576G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00576G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00576G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00576G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00576G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00576G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00576G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00576G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00576G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00576G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00576G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00576G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00576G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00576G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00576G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
