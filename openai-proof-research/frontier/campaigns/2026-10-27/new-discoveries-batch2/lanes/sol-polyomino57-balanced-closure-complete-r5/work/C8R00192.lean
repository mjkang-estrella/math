import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C8R00192_closed (row : List GridPoint) (h : FamilyMember row F8B000L6) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  have c8r192_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r192targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r192choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,5),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r192targets [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4)] c8r192choice = true := by decide
    refine ⟨c8r192targets, c8r192choice, ?_, checked⟩
    intro S h
    simp only [c8r192targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 9 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 7 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 31 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 12 _ (by rfl)))
  have c8r193_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r193targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r193choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,5),(3,(1,0))),((0,-1),(4,(0,1))),((0,3),(5,(0,0))),((0,4),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,6),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r193targets [(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5)] c8r193choice = true := by decide
    refine ⟨c8r193targets, c8r193choice, ?_, checked⟩
    intro S h
    simp only [c8r193targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 10 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 8 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 0 _ (by rfl)))
    · subst S
      exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 21 _ (by rfl)))
  have c8r194_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c8r194targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c8r194choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r194targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)] c8r194choice = true := by decide
    refine ⟨c8r194targets, c8r194choice, ?_, checked⟩
    intro S h
    simp only [c8r194targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 11 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 9 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 21 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 28 _ (by rfl)))
  have c8r195_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)] := by
    let c8r195targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
    let c8r195choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r195targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)] c8r195choice = true := by decide
    refine ⟨c8r195targets, c8r195choice, ?_, checked⟩
    intro S h
    simp only [c8r195targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 12 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 10 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 0 _ (by rfl)))
  have c8r196_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)] := by
    let c8r196targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
    let c8r196choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r196targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)] c8r196choice = true := by decide
    refine ⟨c8r196targets, c8r196choice, ?_, checked⟩
    intro S h
    simp only [c8r196targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 13 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 11 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 3 _ (by rfl)))
  have c8r197_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)] := by
    let c8r197targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
    let c8r197choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r197targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)] c8r197choice = true := by decide
    refine ⟨c8r197targets, c8r197choice, ?_, checked⟩
    intro S h
    simp only [c8r197targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 14 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 12 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 5 _ (by rfl)))
  have c8r198_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)] := by
    let c8r198targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
    let c8r198choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r198targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)] c8r198choice = true := by decide
    refine ⟨c8r198targets, c8r198choice, ?_, checked⟩
    intro S h
    simp only [c8r198targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 15 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 13 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 7 _ (by rfl)))
  have c8r199_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)] := by
    let c8r199targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]]
    let c8r199choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r199targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)] c8r199choice = true := by decide
    refine ⟨c8r199targets, c8r199choice, ?_, checked⟩
    intro S h
    simp only [c8r199targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 16 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 14 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 10 _ (by rfl)))
  have c8r200_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)] := by
    let c8r200targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]]
    let c8r200choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r200targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)] c8r200choice = true := by decide
    refine ⟨c8r200targets, c8r200choice, ?_, checked⟩
    intro S h
    simp only [c8r200targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 17 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 15 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 13 _ (by rfl)))
  have c8r201_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)] := by
    let c8r201targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]]
    let c8r201choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r201targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)] c8r201choice = true := by decide
    refine ⟨c8r201targets, c8r201choice, ?_, checked⟩
    intro S h
    simp only [c8r201targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 18 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 16 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 15 _ (by rfl)))
  have c8r202_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)] := by
    let c8r202targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]]
    let c8r202choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r202targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)] c8r202choice = true := by decide
    refine ⟨c8r202targets, c8r202choice, ?_, checked⟩
    intro S h
    simp only [c8r202targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 19 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 17 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 11 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 18 _ (by rfl)))
  have c8r203_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)] := by
    let c8r203targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]]
    let c8r203choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r203targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)] c8r203choice = true := by decide
    refine ⟨c8r203targets, c8r203choice, ?_, checked⟩
    intro S h
    simp only [c8r203targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 20 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 18 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 12 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 21 _ (by rfl)))
  have c8r204_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)] := by
    let c8r204targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]]
    let c8r204choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r204targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)] c8r204choice = true := by decide
    refine ⟨c8r204targets, c8r204choice, ?_, checked⟩
    intro S h
    simp only [c8r204targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 21 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 19 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 24 _ (by rfl)))
  have c8r205_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)] := by
    let c8r205targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]]
    let c8r205choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r205targets [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)] c8r205choice = true := by decide
    refine ⟨c8r205targets, c8r205choice, ?_, checked⟩
    intro S h
    simp only [c8r205targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 22 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 20 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 27 _ (by rfl)))
  have c8r206_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)] := by
    let c8r206targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)]]
    let c8r206choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r206targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)] c8r206choice = true := by decide
    refine ⟨c8r206targets, c8r206choice, ?_, checked⟩
    intro S h
    simp only [c8r206targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 23 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 21 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 8 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 0 _ (by rfl)))
  have c8r207_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)] := by
    let c8r207targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)]]
    let c8r207choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r207targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)] c8r207choice = true := by decide
    refine ⟨c8r207targets, c8r207choice, ?_, checked⟩
    intro S h
    simp only [c8r207targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 24 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 22 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 9 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 30 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 2 _ (by rfl)))
  have c8r208_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)] := by
    let c8r208targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]]
    let c8r208choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r208targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)] c8r208choice = true := by decide
    refine ⟨c8r208targets, c8r208choice, ?_, checked⟩
    intro S h
    simp only [c8r208targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 25 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 23 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 31 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 10 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 4 _ (by rfl)))
  have c8r209_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1)] := by
    let c8r209targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)]]
    let c8r209choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r209targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1)] c8r209choice = true := by decide
    refine ⟨c8r209targets, c8r209choice, ?_, checked⟩
    intro S h
    simp only [c8r209targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 26 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 24 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 0 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 7 _ (by rfl)))
  have c8r210_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0)] := by
    let c8r210targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)]]
    let c8r210choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r210targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0)] c8r210choice = true := by decide
    refine ⟨c8r210targets, c8r210choice, ?_, checked⟩
    intro S h
    simp only [c8r210targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 27 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 25 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 1 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 9 _ (by rfl)))
  have c8r211_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3)] := by
    let c8r211targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)]]
    let c8r211choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r211targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3)] c8r211choice = true := by decide
    refine ⟨c8r211targets, c8r211choice, ?_, checked⟩
    intro S h
    simp only [c8r211targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 28 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 26 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 13 _ (by rfl)))
  have c8r212_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1)] := by
    let c8r212targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)]]
    let c8r212choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r212targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1)] c8r212choice = true := by decide
    refine ⟨c8r212targets, c8r212choice, ?_, checked⟩
    intro S h
    simp only [c8r212targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 29 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 27 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 16 _ (by rfl)))
  have c8r213_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2)] := by
    let c8r213targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]]
    let c8r213choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r213targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2)] c8r213choice = true := by decide
    refine ⟨c8r213targets, c8r213choice, ?_, checked⟩
    intro S h
    simp only [c8r213targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 30 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 28 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 14 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 4 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 18 _ (by rfl)))
  have c8r214_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1)] := by
    let c8r214targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)]]
    let c8r214choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r214targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1)] c8r214choice = true := by decide
    refine ⟨c8r214targets, c8r214choice, ?_, checked⟩
    intro S h
    simp only [c8r214targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 31 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 29 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 5 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 1 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 21 _ (by rfl)))
  have c8r215_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2)] := by
    let c8r215targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)]]
    let c8r215choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r215targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2)] c8r215choice = true := by decide
    refine ⟨c8r215targets, c8r215choice, ?_, checked⟩
    intro S h
    simp only [c8r215targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 0 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 30 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 6 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 24 _ (by rfl)))
  have c8r216_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1)] := by
    let c8r216targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]]
    let c8r216choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r216targets [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1)] c8r216choice = true := by decide
    refine ⟨c8r216targets, c8r216choice, ?_, checked⟩
    intro S h
    simp only [c8r216targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 1 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 31 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 7 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L21_lift _ (familyLookup_sound F9B000L21 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 27 _ (by rfl)))
  have c8r217_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5)] := by
    let c8r217targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,5),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c8r217choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,6),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r217targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5)] c8r217choice = true := by decide
    refine ⟨c8r217targets, c8r217choice, ?_, checked⟩
    intro S h
    simp only [c8r217targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 2 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 0 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 18 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 15 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 1 _ (by rfl)))
  have c8r218_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0)] := by
    let c8r218targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c8r218choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((3,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r218targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0)] c8r218choice = true := by decide
    refine ⟨c8r218targets, c8r218choice, ?_, checked⟩
    intro S h
    simp only [c8r218targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 3 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 1 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 23 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 29 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 2 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 6 _ (by rfl)))
  have c8r219_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2)] := by
    let c8r219targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c8r219choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r219targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2)] c8r219choice = true := by decide
    refine ⟨c8r219targets, c8r219choice, ?_, checked⟩
    intro S h
    simp only [c8r219targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 4 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 2 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 10 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 24 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 26 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 3 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 7 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 10 _ (by rfl)))
  have c8r220_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3)] := by
    let c8r220targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c8r220choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r220targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3)] c8r220choice = true := by decide
    refine ⟨c8r220targets, c8r220choice, ?_, checked⟩
    intro S h
    simp only [c8r220targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 5 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 3 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 21 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 25 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 23 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 27 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L22_lift _ (familyLookup_sound F9B000L22 [] 31 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 4 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 8 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 12 _ (by rfl)))
  have c8r221_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,4)] := by
    let c8r221targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c8r221choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r221targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,4)] c8r221choice = true := by decide
    refine ⟨c8r221targets, c8r221choice, ?_, checked⟩
    intro S h
    simp only [c8r221targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 6 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 4 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 22 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 12 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 26 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 0 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 5 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 9 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 11 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 13 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 14 _ (by rfl)))
  have c8r222_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1)] := by
    let c8r222targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(3,1)]]
    let c8r222choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r222targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1)] c8r222choice = true := by decide
    refine ⟨c8r222targets, c8r222choice, ?_, checked⟩
    intro S h
    simp only [c8r222targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 7 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 5 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 24 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 13 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 2 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 28 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 16 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 17 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 18 _ (by rfl)))
  have c8r223_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2)] := by
    let c8r223targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,2)]]
    let c8r223choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c8r223targets [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2)] c8r223choice = true := by decide
    refine ⟨c8r223targets, c8r223choice, ?_, checked⟩
    intro S h
    simp only [c8r223targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F9B001_lift _ (F9B001L26_lift _ (familyLookup_sound F9B001L26 [] 8 _ (by rfl)))
    · subst S
      exact F9B002_lift _ (F9B002L34_lift _ (familyLookup_sound F9B002L34 [] 6 _ (by rfl)))
    · subst S
      exact F9B003_lift _ (F9B003L35_lift _ (familyLookup_sound F9B003L35 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 25 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L10_lift _ (familyLookup_sound F9B000L10 [] 14 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L60_lift _ (familyLookup_sound F9B001L60 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 30 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 3 _ (by rfl)))
    · subst S
      exact F9B001_lift _ (F9B001L63_lift _ (familyLookup_sound F9B001L63 [] 29 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 15 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 19 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 20 _ (by rfl)))
    · subst S
      exact F9B000_lift _ (F9B000L23_lift _ (familyLookup_sound F9B000L23 [] 21 _ (by rfl)))
  simp only [F8B000L6, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r192_closed
  · subst row; exact c8r193_closed
  · subst row; exact c8r194_closed
  · subst row; exact c8r195_closed
  · subst row; exact c8r196_closed
  · subst row; exact c8r197_closed
  · subst row; exact c8r198_closed
  · subst row; exact c8r199_closed
  · subst row; exact c8r200_closed
  · subst row; exact c8r201_closed
  · subst row; exact c8r202_closed
  · subst row; exact c8r203_closed
  · subst row; exact c8r204_closed
  · subst row; exact c8r205_closed
  · subst row; exact c8r206_closed
  · subst row; exact c8r207_closed
  · subst row; exact c8r208_closed
  · subst row; exact c8r209_closed
  · subst row; exact c8r210_closed
  · subst row; exact c8r211_closed
  · subst row; exact c8r212_closed
  · subst row; exact c8r213_closed
  · subst row; exact c8r214_closed
  · subst row; exact c8r215_closed
  · subst row; exact c8r216_closed
  · subst row; exact c8r217_closed
  · subst row; exact c8r218_closed
  · subst row; exact c8r219_closed
  · subst row; exact c8r220_closed
  · subst row; exact c8r221_closed
  · subst row; exact c8r222_closed
  · subst row; exact c8r223_closed
end Polyomino57
