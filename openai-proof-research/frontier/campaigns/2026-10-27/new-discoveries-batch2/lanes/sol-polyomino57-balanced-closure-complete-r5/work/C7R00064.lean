import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r64 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1)]
def c7r64targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1)]]
def c7r64choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r64_checked : successorFastRowCheck c7r64targets c7r64 c7r64choice = true := by decide
theorem c7r64_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r64 := by
  refine ⟨c7r64targets, c7r64choice, ?_, c7r64_checked⟩
  intro S h
  simp only [c7r64targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 24 _ (by rfl)))
def c7r65 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4)]
def c7r65targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,4)]]
def c7r65choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r65_checked : successorFastRowCheck c7r65targets c7r65 c7r65choice = true := by decide
theorem c7r65_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r65 := by
  refine ⟨c7r65targets, c7r65choice, ?_, c7r65_checked⟩
  intro S h
  simp only [c7r65targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 29 _ (by rfl)))
def c7r66 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0)]
def c7r66targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0)]]
def c7r66choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r66_checked : successorFastRowCheck c7r66targets c7r66 c7r66choice = true := by decide
theorem c7r66_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r66 := by
  refine ⟨c7r66targets, c7r66choice, ?_, c7r66_checked⟩
  intro S h
  simp only [c7r66targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 1 _ (by rfl)))
def c7r67 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2)]
def c7r67targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2)]]
def c7r67choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r67_checked : successorFastRowCheck c7r67targets c7r67 c7r67choice = true := by decide
theorem c7r67_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r67 := by
  refine ⟨c7r67targets, c7r67choice, ?_, c7r67_checked⟩
  intro S h
  simp only [c7r67targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 4 _ (by rfl)))
def c7r68 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3)]
def c7r68targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3)]]
def c7r68choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r68_checked : successorFastRowCheck c7r68targets c7r68 c7r68choice = true := by decide
theorem c7r68_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r68 := by
  refine ⟨c7r68targets, c7r68choice, ?_, c7r68_checked⟩
  intro S h
  simp only [c7r68targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 6 _ (by rfl)))
def c7r69 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
def c7r69targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,1)]]
def c7r69choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r69_checked : successorFastRowCheck c7r69targets c7r69 c7r69choice = true := by decide
theorem c7r69_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r69 := by
  refine ⟨c7r69targets, c7r69choice, ?_, c7r69_checked⟩
  intro S h
  simp only [c7r69targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 9 _ (by rfl)))
def c7r70 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2)]
def c7r70targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2)]]
def c7r70choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r70_checked : successorFastRowCheck c7r70targets c7r70 c7r70choice = true := by decide
theorem c7r70_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r70 := by
  refine ⟨c7r70targets, c7r70choice, ?_, c7r70_checked⟩
  intro S h
  simp only [c7r70targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 12 _ (by rfl)))
def c7r71 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0)]
def c7r71targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0)]]
def c7r71choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r71_checked : successorFastRowCheck c7r71targets c7r71 c7r71choice = true := by decide
theorem c7r71_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r71 := by
  refine ⟨c7r71targets, c7r71choice, ?_, c7r71_checked⟩
  intro S h
  simp only [c7r71targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 14 _ (by rfl)))
def c7r72 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2)]
def c7r72targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2)]]
def c7r72choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r72_checked : successorFastRowCheck c7r72targets c7r72 c7r72choice = true := by decide
theorem c7r72_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r72 := by
  refine ⟨c7r72targets, c7r72choice, ?_, c7r72_checked⟩
  intro S h
  simp only [c7r72targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 17 _ (by rfl)))
def c7r73 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3)]
def c7r73targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3)]]
def c7r73choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r73_checked : successorFastRowCheck c7r73targets c7r73 c7r73choice = true := by decide
theorem c7r73_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r73 := by
  refine ⟨c7r73targets, c7r73choice, ?_, c7r73_checked⟩
  intro S h
  simp only [c7r73targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 20 _ (by rfl)))
def c7r74 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2)]
def c7r74targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2)]]
def c7r74choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r74_checked : successorFastRowCheck c7r74targets c7r74 c7r74choice = true := by decide
theorem c7r74_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r74 := by
  refine ⟨c7r74targets, c7r74choice, ?_, c7r74_checked⟩
  intro S h
  simp only [c7r74targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 23 _ (by rfl)))
def c7r75 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2)]
def c7r75targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,2)]]
def c7r75choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r75_checked : successorFastRowCheck c7r75targets c7r75 c7r75choice = true := by decide
theorem c7r75_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r75 := by
  refine ⟨c7r75targets, c7r75choice, ?_, c7r75_checked⟩
  intro S h
  simp only [c7r75targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 27 _ (by rfl)))
def c7r76 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0)]
def c7r76targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0)]]
def c7r76choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r76_checked : successorFastRowCheck c7r76targets c7r76 c7r76choice = true := by decide
theorem c7r76_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r76 := by
  refine ⟨c7r76targets, c7r76choice, ?_, c7r76_checked⟩
  intro S h
  simp only [c7r76targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 29 _ (by rfl)))
def c7r77 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1)]
def c7r77targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,1)]]
def c7r77choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r77_checked : successorFastRowCheck c7r77targets c7r77 c7r77choice = true := by decide
theorem c7r77_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r77 := by
  refine ⟨c7r77targets, c7r77choice, ?_, c7r77_checked⟩
  intro S h
  simp only [c7r77targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 31 _ (by rfl)))
def c7r78 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1)]
def c7r78targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1)]]
def c7r78choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r78_checked : successorFastRowCheck c7r78targets c7r78 c7r78choice = true := by decide
theorem c7r78_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r78 := by
  refine ⟨c7r78targets, c7r78choice, ?_, c7r78_checked⟩
  intro S h
  simp only [c7r78targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 2 _ (by rfl)))
def c7r79 : List GridPoint := [(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0)]
def c7r79targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(5,0)]]
def c7r79choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,2),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,-1),(12,(0,1))),((4,1),(13,(0,0))),((5,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r79_checked : successorFastRowCheck c7r79targets c7r79 c7r79choice = true := by decide
theorem c7r79_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r79 := by
  refine ⟨c7r79targets, c7r79choice, ?_, c7r79_checked⟩
  intro S h
  simp only [c7r79targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 4 _ (by rfl)))
def c7r80 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4)]
def c7r80targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r80choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r80_checked : successorFastRowCheck c7r80targets c7r80 c7r80choice = true := by decide
theorem c7r80_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r80 := by
  refine ⟨c7r80targets, c7r80choice, ?_, c7r80_checked⟩
  intro S h
  simp only [c7r80targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 9 _ (by rfl)))
def c7r81 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1)]
def c7r81targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1)]]
def c7r81choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r81_checked : successorFastRowCheck c7r81targets c7r81 c7r81choice = true := by decide
theorem c7r81_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r81 := by
  refine ⟨c7r81targets, c7r81choice, ?_, c7r81_checked⟩
  intro S h
  simp only [c7r81targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 13 _ (by rfl)))
def c7r82 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2)]
def c7r82targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2)]]
def c7r82choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,2),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r82_checked : successorFastRowCheck c7r82targets c7r82 c7r82choice = true := by decide
theorem c7r82_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r82 := by
  refine ⟨c7r82targets, c7r82choice, ?_, c7r82_checked⟩
  intro S h
  simp only [c7r82targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 15 _ (by rfl)))
def c7r83 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3)]
def c7r83targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3)]]
def c7r83choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r83_checked : successorFastRowCheck c7r83targets c7r83 c7r83choice = true := by decide
theorem c7r83_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r83 := by
  refine ⟨c7r83targets, c7r83choice, ?_, c7r83_checked⟩
  intro S h
  simp only [c7r83targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 17 _ (by rfl)))
def c7r84 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1)]
def c7r84targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)]]
def c7r84choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r84_checked : successorFastRowCheck c7r84targets c7r84 c7r84choice = true := by decide
theorem c7r84_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r84 := by
  refine ⟨c7r84targets, c7r84choice, ?_, c7r84_checked⟩
  intro S h
  simp only [c7r84targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 20 _ (by rfl)))
def c7r85 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2)]
def c7r85targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2)]]
def c7r85choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r85_checked : successorFastRowCheck c7r85targets c7r85 c7r85choice = true := by decide
theorem c7r85_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r85 := by
  refine ⟨c7r85targets, c7r85choice, ?_, c7r85_checked⟩
  intro S h
  simp only [c7r85targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 23 _ (by rfl)))
def c7r86 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1)]
def c7r86targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1)]]
def c7r86choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r86_checked : successorFastRowCheck c7r86targets c7r86 c7r86choice = true := by decide
theorem c7r86_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r86 := by
  refine ⟨c7r86targets, c7r86choice, ?_, c7r86_checked⟩
  intro S h
  simp only [c7r86targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 26 _ (by rfl)))
def c7r87 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3)]
def c7r87targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3)]]
def c7r87choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r87_checked : successorFastRowCheck c7r87targets c7r87 c7r87choice = true := by decide
theorem c7r87_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r87 := by
  refine ⟨c7r87targets, c7r87choice, ?_, c7r87_checked⟩
  intro S h
  simp only [c7r87targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 29 _ (by rfl)))
def c7r88 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2)]
def c7r88targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2)]]
def c7r88choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r88_checked : successorFastRowCheck c7r88targets c7r88 c7r88choice = true := by decide
theorem c7r88_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r88 := by
  refine ⟨c7r88targets, c7r88choice, ?_, c7r88_checked⟩
  intro S h
  simp only [c7r88targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 0 _ (by rfl)))
def c7r89 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2)]
def c7r89targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2)]]
def c7r89choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r89_checked : successorFastRowCheck c7r89targets c7r89 c7r89choice = true := by decide
theorem c7r89_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r89 := by
  refine ⟨c7r89targets, c7r89choice, ?_, c7r89_checked⟩
  intro S h
  simp only [c7r89targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 5 _ (by rfl)))
def c7r90 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0)]
def c7r90targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0)]]
def c7r90choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r90_checked : successorFastRowCheck c7r90targets c7r90 c7r90choice = true := by decide
theorem c7r90_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r90 := by
  refine ⟨c7r90targets, c7r90choice, ?_, c7r90_checked⟩
  intro S h
  simp only [c7r90targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 7 _ (by rfl)))
def c7r91 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1)]
def c7r91targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1)]]
def c7r91choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r91_checked : successorFastRowCheck c7r91targets c7r91 c7r91choice = true := by decide
theorem c7r91_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r91 := by
  refine ⟨c7r91targets, c7r91choice, ?_, c7r91_checked⟩
  intro S h
  simp only [c7r91targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 9 _ (by rfl)))
def c7r92 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3)]
def c7r92targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3)]]
def c7r92choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r92_checked : successorFastRowCheck c7r92targets c7r92 c7r92choice = true := by decide
theorem c7r92_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r92 := by
  refine ⟨c7r92targets, c7r92choice, ?_, c7r92_checked⟩
  intro S h
  simp only [c7r92targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 13 _ (by rfl)))
def c7r93 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1)]
def c7r93targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1)]]
def c7r93choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r93_checked : successorFastRowCheck c7r93targets c7r93 c7r93choice = true := by decide
theorem c7r93_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r93 := by
  refine ⟨c7r93targets, c7r93choice, ?_, c7r93_checked⟩
  intro S h
  simp only [c7r93targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 16 _ (by rfl)))
def c7r94 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2)]
def c7r94targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2)]]
def c7r94choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r94_checked : successorFastRowCheck c7r94targets c7r94 c7r94choice = true := by decide
theorem c7r94_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r94 := by
  refine ⟨c7r94targets, c7r94choice, ?_, c7r94_checked⟩
  intro S h
  simp only [c7r94targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 18 _ (by rfl)))
def c7r95 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1)]
def c7r95targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1)]]
def c7r95choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r95_checked : successorFastRowCheck c7r95targets c7r95 c7r95choice = true := by decide
theorem c7r95_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r95 := by
  refine ⟨c7r95targets, c7r95choice, ?_, c7r95_checked⟩
  intro S h
  simp only [c7r95targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 21 _ (by rfl)))
theorem C7R00064_closed (row : List GridPoint) (h : FamilyMember row F7B000L2) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L2, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r64_closed
  · subst row; exact c7r65_closed
  · subst row; exact c7r66_closed
  · subst row; exact c7r67_closed
  · subst row; exact c7r68_closed
  · subst row; exact c7r69_closed
  · subst row; exact c7r70_closed
  · subst row; exact c7r71_closed
  · subst row; exact c7r72_closed
  · subst row; exact c7r73_closed
  · subst row; exact c7r74_closed
  · subst row; exact c7r75_closed
  · subst row; exact c7r76_closed
  · subst row; exact c7r77_closed
  · subst row; exact c7r78_closed
  · subst row; exact c7r79_closed
  · subst row; exact c7r80_closed
  · subst row; exact c7r81_closed
  · subst row; exact c7r82_closed
  · subst row; exact c7r83_closed
  · subst row; exact c7r84_closed
  · subst row; exact c7r85_closed
  · subst row; exact c7r86_closed
  · subst row; exact c7r87_closed
  · subst row; exact c7r88_closed
  · subst row; exact c7r89_closed
  · subst row; exact c7r90_closed
  · subst row; exact c7r91_closed
  · subst row; exact c7r92_closed
  · subst row; exact c7r93_closed
  · subst row; exact c7r94_closed
  · subst row; exact c7r95_closed
end Polyomino57
