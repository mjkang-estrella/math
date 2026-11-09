import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r32 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3)]
def c7r32targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3)]]
def c7r32choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r32_checked : successorFastRowCheck c7r32targets c7r32 c7r32choice = true := by decide
theorem c7r32_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r32 := by
  refine ⟨c7r32targets, c7r32choice, ?_, c7r32_checked⟩
  intro S h
  simp only [c7r32targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 17 _ (by rfl)))
def c7r33 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1)]
def c7r33targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1)]]
def c7r33choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r33_checked : successorFastRowCheck c7r33targets c7r33 c7r33choice = true := by decide
theorem c7r33_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r33 := by
  refine ⟨c7r33targets, c7r33choice, ?_, c7r33_checked⟩
  intro S h
  simp only [c7r33targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 20 _ (by rfl)))
def c7r34 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0)]
def c7r34targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0)]]
def c7r34choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((3,-1),(12,(0,1))),((3,1),(13,(0,0))),((4,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r34_checked : successorFastRowCheck c7r34targets c7r34 c7r34choice = true := by decide
theorem c7r34_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r34 := by
  refine ⟨c7r34targets, c7r34choice, ?_, c7r34_checked⟩
  intro S h
  simp only [c7r34targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 22 _ (by rfl)))
def c7r35 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3)]
def c7r35targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3)]]
def c7r35choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r35_checked : successorFastRowCheck c7r35targets c7r35 c7r35choice = true := by decide
theorem c7r35_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r35 := by
  refine ⟨c7r35targets, c7r35choice, ?_, c7r35_checked⟩
  intro S h
  simp only [c7r35targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 26 _ (by rfl)))
def c7r36 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1)]
def c7r36targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1)]]
def c7r36choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r36_checked : successorFastRowCheck c7r36targets c7r36 c7r36choice = true := by decide
theorem c7r36_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r36 := by
  refine ⟨c7r36targets, c7r36choice, ?_, c7r36_checked⟩
  intro S h
  simp only [c7r36targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 29 _ (by rfl)))
def c7r37 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2)]
def c7r37targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2)]]
def c7r37choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r37_checked : successorFastRowCheck c7r37targets c7r37 c7r37choice = true := by decide
theorem c7r37_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r37 := by
  refine ⟨c7r37targets, c7r37choice, ?_, c7r37_checked⟩
  intro S h
  simp only [c7r37targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 31 _ (by rfl)))
def c7r38 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4)]
def c7r38targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4)]]
def c7r38choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r38_checked : successorFastRowCheck c7r38targets c7r38 c7r38choice = true := by decide
theorem c7r38_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r38 := by
  refine ⟨c7r38targets, c7r38choice, ?_, c7r38_checked⟩
  intro S h
  simp only [c7r38targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 3 _ (by rfl)))
def c7r39 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1)]
def c7r39targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1)]]
def c7r39choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r39_checked : successorFastRowCheck c7r39targets c7r39 c7r39choice = true := by decide
theorem c7r39_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r39 := by
  refine ⟨c7r39targets, c7r39choice, ?_, c7r39_checked⟩
  intro S h
  simp only [c7r39targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 7 _ (by rfl)))
def c7r40 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3)]
def c7r40targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3)]]
def c7r40choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r40_checked : successorFastRowCheck c7r40targets c7r40 c7r40choice = true := by decide
theorem c7r40_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r40 := by
  refine ⟨c7r40targets, c7r40choice, ?_, c7r40_checked⟩
  intro S h
  simp only [c7r40targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 10 _ (by rfl)))
def c7r41 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1)]
def c7r41targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1)]]
def c7r41choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,2),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r41_checked : successorFastRowCheck c7r41targets c7r41 c7r41choice = true := by decide
theorem c7r41_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r41 := by
  refine ⟨c7r41targets, c7r41choice, ?_, c7r41_checked⟩
  intro S h
  simp only [c7r41targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 13 _ (by rfl)))
def c7r42 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2)]
def c7r42targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2)]]
def c7r42choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r42_checked : successorFastRowCheck c7r42targets c7r42 c7r42choice = true := by decide
theorem c7r42_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r42 := by
  refine ⟨c7r42targets, c7r42choice, ?_, c7r42_checked⟩
  intro S h
  simp only [c7r42targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 16 _ (by rfl)))
def c7r43 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1)]
def c7r43targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1)]]
def c7r43choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r43_checked : successorFastRowCheck c7r43targets c7r43 c7r43choice = true := by decide
theorem c7r43_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r43 := by
  refine ⟨c7r43targets, c7r43choice, ?_, c7r43_checked⟩
  intro S h
  simp only [c7r43targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 19 _ (by rfl)))
def c7r44 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4)]
def c7r44targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4)]]
def c7r44choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r44_checked : successorFastRowCheck c7r44targets c7r44 c7r44choice = true := by decide
theorem c7r44_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r44 := by
  refine ⟨c7r44targets, c7r44choice, ?_, c7r44_checked⟩
  intro S h
  simp only [c7r44targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 23 _ (by rfl)))
def c7r45 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2)]
def c7r45targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2)]]
def c7r45choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r45_checked : successorFastRowCheck c7r45targets c7r45 c7r45choice = true := by decide
theorem c7r45_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r45 := by
  refine ⟨c7r45targets, c7r45choice, ?_, c7r45_checked⟩
  intro S h
  simp only [c7r45targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 26 _ (by rfl)))
def c7r46 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def c7r46targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3)]]
def c7r46choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r46_checked : successorFastRowCheck c7r46targets c7r46 c7r46choice = true := by decide
theorem c7r46_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r46 := by
  refine ⟨c7r46targets, c7r46choice, ?_, c7r46_checked⟩
  intro S h
  simp only [c7r46targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 28 _ (by rfl)))
def c7r47 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2)]
def c7r47targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2)]]
def c7r47choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r47_checked : successorFastRowCheck c7r47targets c7r47 c7r47choice = true := by decide
theorem c7r47_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r47 := by
  refine ⟨c7r47targets, c7r47choice, ?_, c7r47_checked⟩
  intro S h
  simp only [c7r47targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 0 _ (by rfl)))
def c7r48 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3)]
def c7r48targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3)]]
def c7r48choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r48_checked : successorFastRowCheck c7r48targets c7r48 c7r48choice = true := by decide
theorem c7r48_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r48 := by
  refine ⟨c7r48targets, c7r48choice, ?_, c7r48_checked⟩
  intro S h
  simp only [c7r48targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 3 _ (by rfl)))
def c7r49 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2)]
def c7r49targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2)]]
def c7r49choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r49_checked : successorFastRowCheck c7r49targets c7r49 c7r49choice = true := by decide
theorem c7r49_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r49 := by
  refine ⟨c7r49targets, c7r49choice, ?_, c7r49_checked⟩
  intro S h
  simp only [c7r49targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 6 _ (by rfl)))
def c7r50 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5)]
def c7r50targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,5)]]
def c7r50choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,6),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r50_checked : successorFastRowCheck c7r50targets c7r50 c7r50choice = true := by decide
theorem c7r50_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r50 := by
  refine ⟨c7r50targets, c7r50choice, ?_, c7r50_checked⟩
  intro S h
  simp only [c7r50targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 10 _ (by rfl)))
def c7r51 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3)]
def c7r51targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3)]]
def c7r51choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r51_checked : successorFastRowCheck c7r51targets c7r51 c7r51choice = true := by decide
theorem c7r51_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r51 := by
  refine ⟨c7r51targets, c7r51choice, ?_, c7r51_checked⟩
  intro S h
  simp only [c7r51targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 13 _ (by rfl)))
def c7r52 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4)]
def c7r52targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4)]]
def c7r52choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r52_checked : successorFastRowCheck c7r52targets c7r52 c7r52choice = true := by decide
theorem c7r52_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r52 := by
  refine ⟨c7r52targets, c7r52choice, ?_, c7r52_checked⟩
  intro S h
  simp only [c7r52targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 15 _ (by rfl)))
def c7r53 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3)]
def c7r53targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3)]]
def c7r53choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r53_checked : successorFastRowCheck c7r53targets c7r53 c7r53choice = true := by decide
theorem c7r53_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r53 := by
  refine ⟨c7r53targets, c7r53choice, ?_, c7r53_checked⟩
  intro S h
  simp only [c7r53targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 19 _ (by rfl)))
def c7r54 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4)]
def c7r54targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,4)]]
def c7r54choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r54_checked : successorFastRowCheck c7r54targets c7r54 c7r54choice = true := by decide
theorem c7r54_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r54 := by
  refine ⟨c7r54targets, c7r54choice, ?_, c7r54_checked⟩
  intro S h
  simp only [c7r54targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 22 _ (by rfl)))
def c7r55 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3)]
def c7r55targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3)]]
def c7r55choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r55_checked : successorFastRowCheck c7r55targets c7r55 c7r55choice = true := by decide
theorem c7r55_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r55 := by
  refine ⟨c7r55targets, c7r55choice, ?_, c7r55_checked⟩
  intro S h
  simp only [c7r55targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 25 _ (by rfl)))
def c7r56 : List GridPoint := [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4)]
def c7r56targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4)]]
def c7r56choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,5),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r56_checked : successorFastRowCheck c7r56targets c7r56 c7r56choice = true := by decide
theorem c7r56_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r56 := by
  refine ⟨c7r56targets, c7r56choice, ?_, c7r56_checked⟩
  intro S h
  simp only [c7r56targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 0 _ (by rfl)))
def c7r57 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3)]
def c7r57targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)]]
def c7r57choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r57_checked : successorFastRowCheck c7r57targets c7r57 c7r57choice = true := by decide
theorem c7r57_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r57 := by
  refine ⟨c7r57targets, c7r57choice, ?_, c7r57_checked⟩
  intro S h
  simp only [c7r57targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 6 _ (by rfl)))
def c7r58 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0)]
def c7r58targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)]]
def c7r58choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((3,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r58_checked : successorFastRowCheck c7r58targets c7r58 c7r58choice = true := by decide
theorem c7r58_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r58 := by
  refine ⟨c7r58targets, c7r58choice, ?_, c7r58_checked⟩
  intro S h
  simp only [c7r58targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 9 _ (by rfl)))
def c7r59 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1)]
def c7r59targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)]]
def c7r59choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r59_checked : successorFastRowCheck c7r59targets c7r59 c7r59choice = true := by decide
theorem c7r59_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r59 := by
  refine ⟨c7r59targets, c7r59choice, ?_, c7r59_checked⟩
  intro S h
  simp only [c7r59targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 11 _ (by rfl)))
def c7r60 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2)]
def c7r60targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)]]
def c7r60choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r60_checked : successorFastRowCheck c7r60targets c7r60 c7r60choice = true := by decide
theorem c7r60_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r60 := by
  refine ⟨c7r60targets, c7r60choice, ?_, c7r60_checked⟩
  intro S h
  simp only [c7r60targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 13 _ (by rfl)))
def c7r61 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1)]
def c7r61targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)]]
def c7r61choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r61_checked : successorFastRowCheck c7r61targets c7r61 c7r61choice = true := by decide
theorem c7r61_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r61 := by
  refine ⟨c7r61targets, c7r61choice, ?_, c7r61_checked⟩
  intro S h
  simp only [c7r61targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 16 _ (by rfl)))
def c7r62 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0)]
def c7r62targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0)]]
def c7r62choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r62_checked : successorFastRowCheck c7r62targets c7r62 c7r62choice = true := by decide
theorem c7r62_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r62 := by
  refine ⟨c7r62targets, c7r62choice, ?_, c7r62_checked⟩
  intro S h
  simp only [c7r62targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 18 _ (by rfl)))
def c7r63 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2)]
def c7r63targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2)]]
def c7r63choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r63_checked : successorFastRowCheck c7r63targets c7r63 c7r63choice = true := by decide
theorem c7r63_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r63 := by
  refine ⟨c7r63targets, c7r63choice, ?_, c7r63_checked⟩
  intro S h
  simp only [c7r63targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 21 _ (by rfl)))
theorem C7R00032_closed (row : List GridPoint) (h : FamilyMember row F7B000L1) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L1, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r32_closed
  · subst row; exact c7r33_closed
  · subst row; exact c7r34_closed
  · subst row; exact c7r35_closed
  · subst row; exact c7r36_closed
  · subst row; exact c7r37_closed
  · subst row; exact c7r38_closed
  · subst row; exact c7r39_closed
  · subst row; exact c7r40_closed
  · subst row; exact c7r41_closed
  · subst row; exact c7r42_closed
  · subst row; exact c7r43_closed
  · subst row; exact c7r44_closed
  · subst row; exact c7r45_closed
  · subst row; exact c7r46_closed
  · subst row; exact c7r47_closed
  · subst row; exact c7r48_closed
  · subst row; exact c7r49_closed
  · subst row; exact c7r50_closed
  · subst row; exact c7r51_closed
  · subst row; exact c7r52_closed
  · subst row; exact c7r53_closed
  · subst row; exact c7r54_closed
  · subst row; exact c7r55_closed
  · subst row; exact c7r56_closed
  · subst row; exact c7r57_closed
  · subst row; exact c7r58_closed
  · subst row; exact c7r59_closed
  · subst row; exact c7r60_closed
  · subst row; exact c7r61_closed
  · subst row; exact c7r62_closed
  · subst row; exact c7r63_closed
end Polyomino57
