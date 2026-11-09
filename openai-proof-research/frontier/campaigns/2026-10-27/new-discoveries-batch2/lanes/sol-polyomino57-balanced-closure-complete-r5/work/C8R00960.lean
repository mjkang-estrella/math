import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00960G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r960_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)] := by
    let c8r960targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c8r960choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r960targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)] c8r960choice = true := by decide
    refine ⟨c8r960targets, c8r960choice, ?_, checked⟩
    intro S h
    simp only [c8r960targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 12 _ (by rfl)))
  have c8r961_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)] := by
    let c8r961targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)]]
    let c8r961choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r961targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)] c8r961choice = true := by decide
    refine ⟨c8r961targets, c8r961choice, ?_, checked⟩
    intro S h
    simp only [c8r961targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 15 _ (by rfl)))
  have c8r962_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)] := by
    let c8r962targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)]]
    let c8r962choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r962targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)] c8r962choice = true := by decide
    refine ⟨c8r962targets, c8r962choice, ?_, checked⟩
    intro S h
    simp only [c8r962targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 18 _ (by rfl)))
  have c8r963_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)] := by
    let c8r963targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c8r963choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r963targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)] c8r963choice = true := by decide
    refine ⟨c8r963targets, c8r963choice, ?_, checked⟩
    intro S h
    simp only [c8r963targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L35_lift _ (familyLookup_sound F9B001L35 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 21 _ (by rfl)))
  have c8r964_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)] := by
    let c8r964targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c8r964choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r964targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)] c8r964choice = true := by decide
    refine ⟨c8r964targets, c8r964choice, ?_, checked⟩
    intro S h
    simp only [c8r964targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 24 _ (by rfl)))
  have c8r965_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)] := by
    let c8r965targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c8r965choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,5),(10,(0,0))),((4,3),(11,(0,0))),((4,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r965targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)] c8r965choice = true := by decide
    refine ⟨c8r965targets, c8r965choice, ?_, checked⟩
    intro S h
    simp only [c8r965targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 27 _ (by rfl)))
  have c8r966_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)] := by
    let c8r966targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c8r966choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r966targets [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)] c8r966choice = true := by decide
    refine ⟨c8r966targets, c8r966choice, ?_, checked⟩
    intro S h
    simp only [c8r966targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 30 _ (by rfl)))
  have c8r967_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c8r967targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c8r967choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r967targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] c8r967choice = true := by decide
    refine ⟨c8r967targets, c8r967choice, ?_, checked⟩
    intro S h
    simp only [c8r967targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L61_lift _ (familyLookup_sound F9B000L61 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 3 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r960_closed
  · subst row; exact c8r961_closed
  · subst row; exact c8r962_closed
  · subst row; exact c8r963_closed
  · subst row; exact c8r964_closed
  · subst row; exact c8r965_closed
  · subst row; exact c8r966_closed
  · subst row; exact c8r967_closed
theorem C8R00960G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r968_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c8r968targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c8r968choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r968targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] c8r968choice = true := by decide
    refine ⟨c8r968targets, c8r968choice, ?_, checked⟩
    intro S h
    simp only [c8r968targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 5 _ (by rfl)))
  have c8r969_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c8r969targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c8r969choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r969targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] c8r969choice = true := by decide
    refine ⟨c8r969targets, c8r969choice, ?_, checked⟩
    intro S h
    simp only [c8r969targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 7 _ (by rfl)))
  have c8r970_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)] := by
    let c8r970targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c8r970choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,4),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r970targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)] c8r970choice = true := by decide
    refine ⟨c8r970targets, c8r970choice, ?_, checked⟩
    intro S h
    simp only [c8r970targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 11 _ (by rfl)))
  have c8r971_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)] := by
    let c8r971targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c8r971choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r971targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)] c8r971choice = true := by decide
    refine ⟨c8r971targets, c8r971choice, ?_, checked⟩
    intro S h
    simp only [c8r971targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L27_lift _ (familyLookup_sound F9B001L27 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 14 _ (by rfl)))
  have c8r972_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)] := by
    let c8r972targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c8r972choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r972targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)] c8r972choice = true := by decide
    refine ⟨c8r972targets, c8r972choice, ?_, checked⟩
    intro S h
    simp only [c8r972targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L32_lift _ (familyLookup_sound F9B001L32 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 16 _ (by rfl)))
  have c8r973_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c8r973targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c8r973choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r973targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] c8r973choice = true := by decide
    refine ⟨c8r973targets, c8r973choice, ?_, checked⟩
    intro S h
    simp only [c8r973targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L48_lift _ (familyLookup_sound F9B000L48 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 19 _ (by rfl)))
  have c8r974_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c8r974targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c8r974choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r974targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)] c8r974choice = true := by decide
    refine ⟨c8r974targets, c8r974choice, ?_, checked⟩
    intro S h
    simp only [c8r974targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 22 _ (by rfl)))
  have c8r975_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] := by
    let c8r975targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]
    let c8r975choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r975targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)] c8r975choice = true := by decide
    refine ⟨c8r975targets, c8r975choice, ?_, checked⟩
    intro S h
    simp only [c8r975targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 25 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r968_closed
  · subst row; exact c8r969_closed
  · subst row; exact c8r970_closed
  · subst row; exact c8r971_closed
  · subst row; exact c8r972_closed
  · subst row; exact c8r973_closed
  · subst row; exact c8r974_closed
  · subst row; exact c8r975_closed
theorem C8R00960G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r976_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] := by
    let c8r976targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c8r976choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,5),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0))),((4,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r976targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)] c8r976choice = true := by decide
    refine ⟨c8r976targets, c8r976choice, ?_, checked⟩
    intro S h
    simp only [c8r976targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 29 _ (by rfl)))
  have c8r977_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] := by
    let c8r977targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c8r977choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,4),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r977targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)] c8r977choice = true := by decide
    refine ⟨c8r977targets, c8r977choice, ?_, checked⟩
    intro S h
    simp only [c8r977targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 0 _ (by rfl)))
  have c8r978_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] := by
    let c8r978targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c8r978choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,4),(8,(0,0))),((4,2),(9,(0,0))),((4,4),(10,(0,0))),((5,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r978targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)] c8r978choice = true := by decide
    refine ⟨c8r978targets, c8r978choice, ?_, checked⟩
    intro S h
    simp only [c8r978targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 2 _ (by rfl)))
  have c8r979_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] := by
    let c8r979targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c8r979choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r979targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)] c8r979choice = true := by decide
    refine ⟨c8r979targets, c8r979choice, ?_, checked⟩
    intro S h
    simp only [c8r979targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 6 _ (by rfl)))
  have c8r980_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] := by
    let c8r980targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c8r980choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,4),(10,(0,0))),((5,2),(11,(0,0))),((5,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r980targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)] c8r980choice = true := by decide
    refine ⟨c8r980targets, c8r980choice, ?_, checked⟩
    intro S h
    simp only [c8r980targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 9 _ (by rfl)))
  have c8r981_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] := by
    let c8r981targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c8r981choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,3),(12,(0,0))),((6,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r981targets [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)] c8r981choice = true := by decide
    refine ⟨c8r981targets, c8r981choice, ?_, checked⟩
    intro S h
    simp only [c8r981targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L37_lift _ (familyLookup_sound F9B002L37 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 12 _ (by rfl)))
  have c8r982_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c8r982targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c8r982choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r982targets [(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)] c8r982choice = true := by decide
    refine ⟨c8r982targets, c8r982choice, ?_, checked⟩
    intro S h
    simp only [c8r982targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L49_lift _ (familyLookup_sound F9B001L49 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L31_lift _ (familyLookup_sound F9B001L31 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L36_lift _ (familyLookup_sound F9B001L36 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 18 _ (by rfl)))
  have c8r983_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c8r983targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c8r983choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r983targets [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] c8r983choice = true := by decide
    refine ⟨c8r983targets, c8r983choice, ?_, checked⟩
    intro S h
    simp only [c8r983targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 24 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r976_closed
  · subst row; exact c8r977_closed
  · subst row; exact c8r978_closed
  · subst row; exact c8r979_closed
  · subst row; exact c8r980_closed
  · subst row; exact c8r981_closed
  · subst row; exact c8r982_closed
  · subst row; exact c8r983_closed
theorem C8R00960G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r984_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c8r984targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c8r984choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r984targets [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] c8r984choice = true := by decide
    refine ⟨c8r984targets, c8r984choice, ?_, checked⟩
    intro S h
    simp only [c8r984targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 27 _ (by rfl)))
  have c8r985_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c8r985targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c8r985choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r985targets [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] c8r985choice = true := by decide
    refine ⟨c8r985targets, c8r985choice, ?_, checked⟩
    intro S h
    simp only [c8r985targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 22 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 29 _ (by rfl)))
  have c8r986_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c8r986targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c8r986choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r986targets [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] c8r986choice = true := by decide
    refine ⟨c8r986targets, c8r986choice, ?_, checked⟩
    intro S h
    simp only [c8r986targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 27 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 31 _ (by rfl)))
  have c8r987_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c8r987targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c8r987choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r987targets [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] c8r987choice = true := by decide
    refine ⟨c8r987targets, c8r987choice, ?_, checked⟩
    intro S h
    simp only [c8r987targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L56_lift _ (familyLookup_sound F9B002L56 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 2 _ (by rfl)))
  have c8r988_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c8r988targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c8r988choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r988targets [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] c8r988choice = true := by decide
    refine ⟨c8r988targets, c8r988choice, ?_, checked⟩
    intro S h
    simp only [c8r988targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 4 _ (by rfl)))
  have c8r989_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c8r989targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c8r989choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r989targets [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] c8r989choice = true := by decide
    refine ⟨c8r989targets, c8r989choice, ?_, checked⟩
    intro S h
    simp only [c8r989targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 28 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 7 _ (by rfl)))
  have c8r990_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c8r990targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c8r990choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r990targets [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] c8r990choice = true := by decide
    refine ⟨c8r990targets, c8r990choice, ?_, checked⟩
    intro S h
    simp only [c8r990targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 18 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 17 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L57_lift _ (familyLookup_sound F9B002L57 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 10 _ (by rfl)))
  have c8r991_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)] := by
    let c8r991targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c8r991choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,5),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r991targets [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)] c8r991choice = true := by decide
    refine ⟨c8r991targets, c8r991choice, ?_, checked⟩
    intro S h
    simp only [c8r991targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L50_lift _ (familyLookup_sound F9B001L50 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L62_lift _ (familyLookup_sound F9B000L62 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L49_lift _ (familyLookup_sound F9B000L49 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L38_lift _ (familyLookup_sound F9B002L38 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L28_lift _ (familyLookup_sound F9B001L28 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L33_lift _ (familyLookup_sound F9B001L33 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L37_lift _ (familyLookup_sound F9B001L37 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 19 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L38_lift _ (familyLookup_sound F9B001L38 [] 20 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L39_lift _ (familyLookup_sound F9B001L39 [] 15 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c8r984_closed
  · subst row; exact c8r985_closed
  · subst row; exact c8r986_closed
  · subst row; exact c8r987_closed
  · subst row; exact c8r988_closed
  · subst row; exact c8r989_closed
  · subst row; exact c8r990_closed
  · subst row; exact c8r991_closed
theorem C8R00960_closed (row : List GridPoint) (h : FamilyMember row F8B000L30) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L30, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C8R00960G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00960G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00960G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00960G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00960G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00960G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00960G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00960G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00960G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00960G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00960G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00960G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00960G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00960G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00960G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00960G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00960G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00960G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00960G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00960G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00960G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00960G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00960G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00960G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C8R00960G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C8R00960G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C8R00960G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C8R00960G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C8R00960G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C8R00960G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C8R00960G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C8R00960G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
