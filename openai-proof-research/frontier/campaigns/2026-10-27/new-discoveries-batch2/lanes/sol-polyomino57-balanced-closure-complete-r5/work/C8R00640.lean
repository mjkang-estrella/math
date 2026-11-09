import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00640G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r640_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] := by
    let c8r640targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c8r640choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r640targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] c8r640choice = true := by decide
    refine ⟨c8r640targets, c8r640choice, ?_, checked⟩
    intro S h
    simp only [c8r640targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 17 _ (by rfl)))
  have c8r641_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] := by
    let c8r641targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c8r641choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r641targets [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] c8r641choice = true := by decide
    refine ⟨c8r641targets, c8r641choice, ?_, checked⟩
    intro S h
    simp only [c8r641targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L47_lift _ (familyLookup_sound F9B000L47 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L19_lift _ (familyLookup_sound F9B002L19 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 20 _ (by rfl)))
  have c8r642_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c8r642targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c8r642choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,6),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r642targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)] c8r642choice = true := by decide
    refine ⟨c8r642targets, c8r642choice, ?_, checked⟩
    intro S h
    simp only [c8r642targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 26 _ (by rfl)))
  have c8r643_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c8r643targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c8r643choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0))),((4,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r643targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)] c8r643choice = true := by decide
    refine ⟨c8r643targets, c8r643choice, ?_, checked⟩
    intro S h
    simp only [c8r643targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 31 _ (by rfl)))
  have c8r644_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c8r644targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c8r644choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r644targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)] c8r644choice = true := by decide
    refine ⟨c8r644targets, c8r644choice, ?_, checked⟩
    intro S h
    simp only [c8r644targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 2 _ (by rfl)))
  have c8r645_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c8r645targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c8r645choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r645targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)] c8r645choice = true := by decide
    refine ⟨c8r645targets, c8r645choice, ?_, checked⟩
    intro S h
    simp only [c8r645targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 4 _ (by rfl)))
  have c8r646_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c8r646targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c8r646choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,5),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r646targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)] c8r646choice = true := by decide
    refine ⟨c8r646targets, c8r646choice, ?_, checked⟩
    intro S h
    simp only [c8r646targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L30_lift _ (familyLookup_sound F9B000L30 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 6 _ (by rfl)))
  have c8r647_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c8r647targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c8r647choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r647targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] c8r647choice = true := by decide
    refine ⟨c8r647targets, c8r647choice, ?_, checked⟩
    intro S h
    simp only [c8r647targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L59_lift _ (familyLookup_sound F9B000L59 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L63_lift _ (familyLookup_sound F9B000L63 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 10 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r640_closed
  · subst row; exact c8r641_closed
  · subst row; exact c8r642_closed
  · subst row; exact c8r643_closed
  · subst row; exact c8r644_closed
  · subst row; exact c8r645_closed
  · subst row; exact c8r646_closed
  · subst row; exact c8r647_closed
theorem C8R00640G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r648_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)] := by
    let c8r648targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c8r648choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r648targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)] c8r648choice = true := by decide
    refine ⟨c8r648targets, c8r648choice, ?_, checked⟩
    intro S h
    simp only [c8r648targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 13 _ (by rfl)))
  have c8r649_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)] := by
    let c8r649targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)]]
    let c8r649choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r649targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)] c8r649choice = true := by decide
    refine ⟨c8r649targets, c8r649choice, ?_, checked⟩
    intro S h
    simp only [c8r649targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 16 _ (by rfl)))
  have c8r650_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)] := by
    let c8r650targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)]]
    let c8r650choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0))),((4,2),(13,(0,0))),((5,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r650targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)] c8r650choice = true := by decide
    refine ⟨c8r650targets, c8r650choice, ?_, checked⟩
    intro S h
    simp only [c8r650targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L2_lift _ (familyLookup_sound F9B001L2 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 19 _ (by rfl)))
  have c8r651_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)] := by
    let c8r651targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c8r651choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r651targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)] c8r651choice = true := by decide
    refine ⟨c8r651targets, c8r651choice, ?_, checked⟩
    intro S h
    simp only [c8r651targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 22 _ (by rfl)))
  have c8r652_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)] := by
    let c8r652targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c8r652choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r652targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)] c8r652choice = true := by decide
    refine ⟨c8r652targets, c8r652choice, ?_, checked⟩
    intro S h
    simp only [c8r652targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 25 _ (by rfl)))
  have c8r653_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)] := by
    let c8r653targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c8r653choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,5),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r653targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)] c8r653choice = true := by decide
    refine ⟨c8r653targets, c8r653choice, ?_, checked⟩
    intro S h
    simp only [c8r653targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 28 _ (by rfl)))
  have c8r654_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)] := by
    let c8r654targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c8r654choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,4),(13,(0,0))),((5,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r654targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)] c8r654choice = true := by decide
    refine ⟨c8r654targets, c8r654choice, ?_, checked⟩
    intro S h
    simp only [c8r654targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 31 _ (by rfl)))
  have c8r655_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r655targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r655choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r655targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] c8r655choice = true := by decide
    refine ⟨c8r655targets, c8r655choice, ?_, checked⟩
    intro S h
    simp only [c8r655targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 4 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r648_closed
  · subst row; exact c8r649_closed
  · subst row; exact c8r650_closed
  · subst row; exact c8r651_closed
  · subst row; exact c8r652_closed
  · subst row; exact c8r653_closed
  · subst row; exact c8r654_closed
  · subst row; exact c8r655_closed
theorem C8R00640G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r656_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c8r656targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c8r656choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r656targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] c8r656choice = true := by decide
    refine ⟨c8r656targets, c8r656choice, ?_, checked⟩
    intro S h
    simp only [c8r656targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 6 _ (by rfl)))
  have c8r657_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c8r657targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c8r657choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r657targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] c8r657choice = true := by decide
    refine ⟨c8r657targets, c8r657choice, ?_, checked⟩
    intro S h
    simp only [c8r657targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 8 _ (by rfl)))
  have c8r658_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)] := by
    let c8r658targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c8r658choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r658targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)] c8r658choice = true := by decide
    refine ⟨c8r658targets, c8r658choice, ?_, checked⟩
    intro S h
    simp only [c8r658targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 12 _ (by rfl)))
  have c8r659_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)] := by
    let c8r659targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c8r659choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r659targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)] c8r659choice = true := by decide
    refine ⟨c8r659targets, c8r659choice, ?_, checked⟩
    intro S h
    simp only [c8r659targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 15 _ (by rfl)))
  have c8r660_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)] := by
    let c8r660targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c8r660choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r660targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)] c8r660choice = true := by decide
    refine ⟨c8r660targets, c8r660choice, ?_, checked⟩
    intro S h
    simp only [c8r660targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 17 _ (by rfl)))
  have c8r661_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c8r661targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c8r661choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r661targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] c8r661choice = true := by decide
    refine ⟨c8r661targets, c8r661choice, ?_, checked⟩
    intro S h
    simp only [c8r661targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 20 _ (by rfl)))
  have c8r662_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c8r662targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c8r662choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r662targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] c8r662choice = true := by decide
    refine ⟨c8r662targets, c8r662choice, ?_, checked⟩
    intro S h
    simp only [c8r662targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 23 _ (by rfl)))
  have c8r663_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] := by
    let c8r663targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]
    let c8r663choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r663targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] c8r663choice = true := by decide
    refine ⟨c8r663targets, c8r663choice, ?_, checked⟩
    intro S h
    simp only [c8r663targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 26 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r656_closed
  · subst row; exact c8r657_closed
  · subst row; exact c8r658_closed
  · subst row; exact c8r659_closed
  · subst row; exact c8r660_closed
  · subst row; exact c8r661_closed
  · subst row; exact c8r662_closed
  · subst row; exact c8r663_closed
theorem C8R00640G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r664_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] := by
    let c8r664targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c8r664choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r664targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] c8r664choice = true := by decide
    refine ⟨c8r664targets, c8r664choice, ?_, checked⟩
    intro S h
    simp only [c8r664targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L47_lift _ (familyLookup_sound F9B002L47 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 30 _ (by rfl)))
  have c8r665_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] := by
    let c8r665targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c8r665choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r665targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] c8r665choice = true := by decide
    refine ⟨c8r665targets, c8r665choice, ?_, checked⟩
    intro S h
    simp only [c8r665targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 1 _ (by rfl)))
  have c8r666_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] := by
    let c8r666targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c8r666choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,4),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r666targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] c8r666choice = true := by decide
    refine ⟨c8r666targets, c8r666choice, ?_, checked⟩
    intro S h
    simp only [c8r666targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 3 _ (by rfl)))
  have c8r667_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] := by
    let c8r667targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c8r667choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r667targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] c8r667choice = true := by decide
    refine ⟨c8r667targets, c8r667choice, ?_, checked⟩
    intro S h
    simp only [c8r667targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 7 _ (by rfl)))
  have c8r668_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] := by
    let c8r668targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c8r668choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r668targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] c8r668choice = true := by decide
    refine ⟨c8r668targets, c8r668choice, ?_, checked⟩
    intro S h
    simp only [c8r668targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 10 _ (by rfl)))
  have c8r669_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] := by
    let c8r669targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c8r669choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r669targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] c8r669choice = true := by decide
    refine ⟨c8r669targets, c8r669choice, ?_, checked⟩
    intro S h
    simp only [c8r669targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 13 _ (by rfl)))
  have c8r670_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c8r670targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c8r670choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,4),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r670targets [(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] c8r670choice = true := by decide
    refine ⟨c8r670targets, c8r670choice, ?_, checked⟩
    intro S h
    simp only [c8r670targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L37_lift _ (familyLookup_sound F9B000L37 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L0_lift _ (familyLookup_sound F9B001L0 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L3_lift _ (familyLookup_sound F9B001L3 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 19 _ (by rfl)))
  have c8r671_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r671targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r671choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r671targets [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] c8r671choice = true := by decide
    refine ⟨c8r671targets, c8r671choice, ?_, checked⟩
    intro S h
    simp only [c8r671targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L40_lift _ (familyLookup_sound F9B001L40 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L48_lift _ (familyLookup_sound F9B002L48 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L38_lift _ (familyLookup_sound F9B000L38 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L31_lift _ (familyLookup_sound F9B000L31 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L60_lift _ (familyLookup_sound F9B000L60 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L1_lift _ (familyLookup_sound F9B001L1 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L4_lift _ (familyLookup_sound F9B001L4 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L20_lift _ (familyLookup_sound F9B002L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L5_lift _ (familyLookup_sound F9B001L5 [] 25 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r664_closed
  · subst row; exact c8r665_closed
  · subst row; exact c8r666_closed
  · subst row; exact c8r667_closed
  · subst row; exact c8r668_closed
  · subst row; exact c8r669_closed
  · subst row; exact c8r670_closed
  · subst row; exact c8r671_closed
theorem C8R00640_closed (row : List GridPoint) (h : FamilyMember row F8B000L20) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L20, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00640G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00640G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00640G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00640G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00640G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00640G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00640G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00640G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00640G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00640G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00640G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00640G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00640G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00640G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00640G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00640G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00640G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00640G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00640G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00640G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00640G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00640G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00640G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00640G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00640G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00640G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00640G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00640G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00640G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00640G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00640G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00640G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
