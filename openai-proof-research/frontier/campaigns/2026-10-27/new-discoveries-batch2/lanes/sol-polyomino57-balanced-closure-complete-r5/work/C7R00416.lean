import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r416 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1)]
def c7r416targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r416choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r416_checked : successorFastRowCheck c7r416targets c7r416 c7r416choice = true := by decide
theorem c7r416_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r416 := by
  refine ⟨c7r416targets, c7r416choice, ?_, c7r416_checked⟩
  intro S h
  simp only [c7r416targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 27 _ (by rfl)))
def c7r417 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2)]
def c7r417targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]]
def c7r417choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r417_checked : successorFastRowCheck c7r417targets c7r417 c7r417choice = true := by decide
theorem c7r417_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r417 := by
  refine ⟨c7r417targets, c7r417choice, ?_, c7r417_checked⟩
  intro S h
  simp only [c7r417targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 0 _ (by rfl)))
def c7r418 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0)]
def c7r418targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]]
def c7r418choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r418_checked : successorFastRowCheck c7r418targets c7r418 c7r418choice = true := by decide
theorem c7r418_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r418 := by
  refine ⟨c7r418targets, c7r418choice, ?_, c7r418_checked⟩
  intro S h
  simp only [c7r418targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 2 _ (by rfl)))
def c7r419 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1)]
def c7r419targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]
def c7r419choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r419_checked : successorFastRowCheck c7r419targets c7r419 c7r419choice = true := by decide
theorem c7r419_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r419 := by
  refine ⟨c7r419targets, c7r419choice, ?_, c7r419_checked⟩
  intro S h
  simp only [c7r419targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 4 _ (by rfl)))
def c7r420 : List GridPoint := [(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1)]
def c7r420targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]]
def c7r420choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r420_checked : successorFastRowCheck c7r420targets c7r420 c7r420choice = true := by decide
theorem c7r420_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r420 := by
  refine ⟨c7r420targets, c7r420choice, ?_, c7r420_checked⟩
  intro S h
  simp only [c7r420targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 8 _ (by rfl)))
def c7r421 : List GridPoint := [(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2)]
def c7r421targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
def c7r421choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r421_checked : successorFastRowCheck c7r421targets c7r421 c7r421choice = true := by decide
theorem c7r421_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r421 := by
  refine ⟨c7r421targets, c7r421choice, ?_, c7r421_checked⟩
  intro S h
  simp only [c7r421targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 14 _ (by rfl)))
def c7r422 : List GridPoint := [(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3)]
def c7r422targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r422choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r422_checked : successorFastRowCheck c7r422targets c7r422 c7r422choice = true := by decide
theorem c7r422_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r422 := by
  refine ⟨c7r422targets, c7r422choice, ?_, c7r422_checked⟩
  intro S h
  simp only [c7r422targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 21 _ (by rfl)))
def c7r423 : List GridPoint := [(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0)]
def c7r423targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r423choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r423_checked : successorFastRowCheck c7r423targets c7r423 c7r423choice = true := by decide
theorem c7r423_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r423 := by
  refine ⟨c7r423targets, c7r423choice, ?_, c7r423_checked⟩
  intro S h
  simp only [c7r423targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 24 _ (by rfl)))
def c7r424 : List GridPoint := [(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1)]
def c7r424targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r424choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r424_checked : successorFastRowCheck c7r424targets c7r424 c7r424choice = true := by decide
theorem c7r424_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r424 := by
  refine ⟨c7r424targets, c7r424choice, ?_, c7r424_checked⟩
  intro S h
  simp only [c7r424targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 26 _ (by rfl)))
def c7r425 : List GridPoint := [(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2)]
def c7r425targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r425choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r425_checked : successorFastRowCheck c7r425targets c7r425 c7r425choice = true := by decide
theorem c7r425_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r425 := by
  refine ⟨c7r425targets, c7r425choice, ?_, c7r425_checked⟩
  intro S h
  simp only [c7r425targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 28 _ (by rfl)))
def c7r426 : List GridPoint := [(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1)]
def c7r426targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r426choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r426_checked : successorFastRowCheck c7r426targets c7r426 c7r426choice = true := by decide
theorem c7r426_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r426 := by
  refine ⟨c7r426targets, c7r426choice, ?_, c7r426_checked⟩
  intro S h
  simp only [c7r426targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 1 _ (by rfl)))
def c7r427 : List GridPoint := [(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2)]
def c7r427targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
def c7r427choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r427_checked : successorFastRowCheck c7r427targets c7r427 c7r427choice = true := by decide
theorem c7r427_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r427 := by
  refine ⟨c7r427targets, c7r427choice, ?_, c7r427_checked⟩
  intro S h
  simp only [c7r427targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 7 _ (by rfl)))
def c7r428 : List GridPoint := [(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)]
def c7r428targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)]]
def c7r428choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r428_checked : successorFastRowCheck c7r428targets c7r428 c7r428choice = true := by decide
theorem c7r428_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r428 := by
  refine ⟨c7r428targets, c7r428choice, ?_, c7r428_checked⟩
  intro S h
  simp only [c7r428targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 15 _ (by rfl)))
def c7r429 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r429targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r429choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r429_checked : successorFastRowCheck c7r429targets c7r429 c7r429choice = true := by decide
theorem c7r429_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r429 := by
  refine ⟨c7r429targets, c7r429choice, ?_, c7r429_checked⟩
  intro S h
  simp only [c7r429targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 22 _ (by rfl)))
def c7r430 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)]
def c7r430targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
def c7r430choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r430_checked : successorFastRowCheck c7r430targets c7r430 c7r430choice = true := by decide
theorem c7r430_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r430 := by
  refine ⟨c7r430targets, c7r430choice, ?_, c7r430_checked⟩
  intro S h
  simp only [c7r430targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 26 _ (by rfl)))
def c7r431 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)]
def c7r431targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
def c7r431choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r431_checked : successorFastRowCheck c7r431targets c7r431 c7r431choice = true := by decide
theorem c7r431_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r431 := by
  refine ⟨c7r431targets, c7r431choice, ?_, c7r431_checked⟩
  intro S h
  simp only [c7r431targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 29 _ (by rfl)))
def c7r432 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)]
def c7r432targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
def c7r432choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r432_checked : successorFastRowCheck c7r432targets c7r432 c7r432choice = true := by decide
theorem c7r432_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r432 := by
  refine ⟨c7r432targets, c7r432choice, ?_, c7r432_checked⟩
  intro S h
  simp only [c7r432targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 31 _ (by rfl)))
def c7r433 : List GridPoint := [(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]
def c7r433targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
def c7r433choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r433_checked : successorFastRowCheck c7r433targets c7r433 c7r433choice = true := by decide
theorem c7r433_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r433 := by
  refine ⟨c7r433targets, c7r433choice, ?_, c7r433_checked⟩
  intro S h
  simp only [c7r433targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 1 _ (by rfl)))
def c7r434 : List GridPoint := [(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)]
def c7r434targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
def c7r434choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r434_checked : successorFastRowCheck c7r434targets c7r434 c7r434choice = true := by decide
theorem c7r434_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r434 := by
  refine ⟨c7r434targets, c7r434choice, ?_, c7r434_checked⟩
  intro S h
  simp only [c7r434targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 7 _ (by rfl)))
def c7r435 : List GridPoint := [(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r435targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r435choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r435_checked : successorFastRowCheck c7r435targets c7r435 c7r435choice = true := by decide
theorem c7r435_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r435 := by
  refine ⟨c7r435targets, c7r435choice, ?_, c7r435_checked⟩
  intro S h
  simp only [c7r435targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 16 _ (by rfl)))
def c7r436 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def c7r436targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
def c7r436choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,6),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r436_checked : successorFastRowCheck c7r436targets c7r436 c7r436choice = true := by decide
theorem c7r436_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r436 := by
  refine ⟨c7r436targets, c7r436choice, ?_, c7r436_checked⟩
  intro S h
  simp only [c7r436targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 25 _ (by rfl)))
def c7r437 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def c7r437targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
def c7r437choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r437_checked : successorFastRowCheck c7r437targets c7r437 c7r437choice = true := by decide
theorem c7r437_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r437 := by
  refine ⟨c7r437targets, c7r437choice, ?_, c7r437_checked⟩
  intro S h
  simp only [c7r437targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 30 _ (by rfl)))
def c7r438 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def c7r438targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
def c7r438choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r438_checked : successorFastRowCheck c7r438targets c7r438 c7r438choice = true := by decide
theorem c7r438_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r438 := by
  refine ⟨c7r438targets, c7r438choice, ?_, c7r438_checked⟩
  intro S h
  simp only [c7r438targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 2 _ (by rfl)))
def c7r439 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def c7r439targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
def c7r439choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r439_checked : successorFastRowCheck c7r439targets c7r439 c7r439choice = true := by decide
theorem c7r439_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r439 := by
  refine ⟨c7r439targets, c7r439choice, ?_, c7r439_checked⟩
  intro S h
  simp only [c7r439targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 5 _ (by rfl)))
def c7r440 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def c7r440targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
def c7r440choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r440_checked : successorFastRowCheck c7r440targets c7r440 c7r440choice = true := by decide
theorem c7r440_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r440 := by
  refine ⟨c7r440targets, c7r440choice, ?_, c7r440_checked⟩
  intro S h
  simp only [c7r440targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 7 _ (by rfl)))
def c7r441 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def c7r441targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
def c7r441choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r441_checked : successorFastRowCheck c7r441targets c7r441 c7r441choice = true := by decide
theorem c7r441_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r441 := by
  refine ⟨c7r441targets, c7r441choice, ?_, c7r441_checked⟩
  intro S h
  simp only [c7r441targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 9 _ (by rfl)))
def c7r442 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]
def c7r442targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
def c7r442choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r442_checked : successorFastRowCheck c7r442targets c7r442 c7r442choice = true := by decide
theorem c7r442_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r442 := by
  refine ⟨c7r442targets, c7r442choice, ?_, c7r442_checked⟩
  intro S h
  simp only [c7r442targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 13 _ (by rfl)))
def c7r443 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)]
def c7r443targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
def c7r443choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r443_checked : successorFastRowCheck c7r443targets c7r443 c7r443choice = true := by decide
theorem c7r443_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r443 := by
  refine ⟨c7r443targets, c7r443choice, ?_, c7r443_checked⟩
  intro S h
  simp only [c7r443targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 16 _ (by rfl)))
def c7r444 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)]
def c7r444targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
def c7r444choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r444_checked : successorFastRowCheck c7r444targets c7r444 c7r444choice = true := by decide
theorem c7r444_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r444 := by
  refine ⟨c7r444targets, c7r444choice, ?_, c7r444_checked⟩
  intro S h
  simp only [c7r444targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 19 _ (by rfl)))
def c7r445 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]
def c7r445targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
def c7r445choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r445_checked : successorFastRowCheck c7r445targets c7r445 c7r445choice = true := by decide
theorem c7r445_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r445 := by
  refine ⟨c7r445targets, c7r445choice, ?_, c7r445_checked⟩
  intro S h
  simp only [c7r445targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 21 _ (by rfl)))
def c7r446 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]
def c7r446targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
def c7r446choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r446_checked : successorFastRowCheck c7r446targets c7r446 c7r446choice = true := by decide
theorem c7r446_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r446 := by
  refine ⟨c7r446targets, c7r446choice, ?_, c7r446_checked⟩
  intro S h
  simp only [c7r446targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 24 _ (by rfl)))
def c7r447 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)]
def c7r447targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
def c7r447choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r447_checked : successorFastRowCheck c7r447targets c7r447 c7r447choice = true := by decide
theorem c7r447_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r447 := by
  refine ⟨c7r447targets, c7r447choice, ?_, c7r447_checked⟩
  intro S h
  simp only [c7r447targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 27 _ (by rfl)))
theorem C7R00416_closed (row : List GridPoint) (h : FamilyMember row F7B000L13) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L13, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r416_closed
  · subst row; exact c7r417_closed
  · subst row; exact c7r418_closed
  · subst row; exact c7r419_closed
  · subst row; exact c7r420_closed
  · subst row; exact c7r421_closed
  · subst row; exact c7r422_closed
  · subst row; exact c7r423_closed
  · subst row; exact c7r424_closed
  · subst row; exact c7r425_closed
  · subst row; exact c7r426_closed
  · subst row; exact c7r427_closed
  · subst row; exact c7r428_closed
  · subst row; exact c7r429_closed
  · subst row; exact c7r430_closed
  · subst row; exact c7r431_closed
  · subst row; exact c7r432_closed
  · subst row; exact c7r433_closed
  · subst row; exact c7r434_closed
  · subst row; exact c7r435_closed
  · subst row; exact c7r436_closed
  · subst row; exact c7r437_closed
  · subst row; exact c7r438_closed
  · subst row; exact c7r439_closed
  · subst row; exact c7r440_closed
  · subst row; exact c7r441_closed
  · subst row; exact c7r442_closed
  · subst row; exact c7r443_closed
  · subst row; exact c7r444_closed
  · subst row; exact c7r445_closed
  · subst row; exact c7r446_closed
  · subst row; exact c7r447_closed
end Polyomino57
