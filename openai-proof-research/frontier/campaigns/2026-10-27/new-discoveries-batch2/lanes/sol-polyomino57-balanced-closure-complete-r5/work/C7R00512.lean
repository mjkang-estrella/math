import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r512 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)]
def c7r512targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r512choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r512_checked : successorFastRowCheck c7r512targets c7r512 c7r512choice = true := by decide
theorem c7r512_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r512 := by
  refine ⟨c7r512targets, c7r512choice, ?_, c7r512_checked⟩
  intro S h
  simp only [c7r512targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 12 _ (by rfl)))
def c7r513 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)]
def c7r513targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r513choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r513_checked : successorFastRowCheck c7r513targets c7r513 c7r513choice = true := by decide
theorem c7r513_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r513 := by
  refine ⟨c7r513targets, c7r513choice, ?_, c7r513_checked⟩
  intro S h
  simp only [c7r513targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 14 _ (by rfl)))
def c7r514 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]
def c7r514targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r514choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r514_checked : successorFastRowCheck c7r514targets c7r514 c7r514choice = true := by decide
theorem c7r514_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r514 := by
  refine ⟨c7r514targets, c7r514choice, ?_, c7r514_checked⟩
  intro S h
  simp only [c7r514targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 16 _ (by rfl)))
def c7r515 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)]
def c7r515targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)]]
def c7r515choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r515_checked : successorFastRowCheck c7r515targets c7r515 c7r515choice = true := by decide
theorem c7r515_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r515 := by
  refine ⟨c7r515targets, c7r515choice, ?_, c7r515_checked⟩
  intro S h
  simp only [c7r515targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 19 _ (by rfl)))
def c7r516 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]
def c7r516targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)]]
def c7r516choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r516_checked : successorFastRowCheck c7r516targets c7r516 c7r516choice = true := by decide
theorem c7r516_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r516 := by
  refine ⟨c7r516targets, c7r516choice, ?_, c7r516_checked⟩
  intro S h
  simp only [c7r516targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 21 _ (by rfl)))
def c7r517 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)]
def c7r517targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)]]
def c7r517choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r517_checked : successorFastRowCheck c7r517targets c7r517 c7r517choice = true := by decide
theorem c7r517_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r517 := by
  refine ⟨c7r517targets, c7r517choice, ?_, c7r517_checked⟩
  intro S h
  simp only [c7r517targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 24 _ (by rfl)))
def c7r518 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]
def c7r518targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)]]
def c7r518choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r518_checked : successorFastRowCheck c7r518targets c7r518 c7r518choice = true := by decide
theorem c7r518_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r518 := by
  refine ⟨c7r518targets, c7r518choice, ?_, c7r518_checked⟩
  intro S h
  simp only [c7r518targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 27 _ (by rfl)))
def c7r519 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)]
def c7r519targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r519choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r519_checked : successorFastRowCheck c7r519targets c7r519 c7r519choice = true := by decide
theorem c7r519_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r519 := by
  refine ⟨c7r519targets, c7r519choice, ?_, c7r519_checked⟩
  intro S h
  simp only [c7r519targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 0 _ (by rfl)))
def c7r520 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)]
def c7r520targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)]]
def c7r520choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r520_checked : successorFastRowCheck c7r520targets c7r520 c7r520choice = true := by decide
theorem c7r520_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r520 := by
  refine ⟨c7r520targets, c7r520choice, ?_, c7r520_checked⟩
  intro S h
  simp only [c7r520targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 5 _ (by rfl)))
def c7r521 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)]
def c7r521targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)]]
def c7r521choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r521_checked : successorFastRowCheck c7r521targets c7r521 c7r521choice = true := by decide
theorem c7r521_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r521 := by
  refine ⟨c7r521targets, c7r521choice, ?_, c7r521_checked⟩
  intro S h
  simp only [c7r521targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 7 _ (by rfl)))
def c7r522 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]
def c7r522targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)]]
def c7r522choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r522_checked : successorFastRowCheck c7r522targets c7r522 c7r522choice = true := by decide
theorem c7r522_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r522 := by
  refine ⟨c7r522targets, c7r522choice, ?_, c7r522_checked⟩
  intro S h
  simp only [c7r522targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 9 _ (by rfl)))
def c7r523 : List GridPoint := [(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)]
def c7r523targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)]]
def c7r523choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r523_checked : successorFastRowCheck c7r523targets c7r523 c7r523choice = true := by decide
theorem c7r523_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r523 := by
  refine ⟨c7r523targets, c7r523choice, ?_, c7r523_checked⟩
  intro S h
  simp only [c7r523targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 13 _ (by rfl)))
def c7r524 : List GridPoint := [(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)]
def c7r524targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
def c7r524choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r524_checked : successorFastRowCheck c7r524targets c7r524 c7r524choice = true := by decide
theorem c7r524_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r524 := by
  refine ⟨c7r524targets, c7r524choice, ?_, c7r524_checked⟩
  intro S h
  simp only [c7r524targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 19 _ (by rfl)))
def c7r525 : List GridPoint := [(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)]
def c7r525targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r525choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r525_checked : successorFastRowCheck c7r525targets c7r525 c7r525choice = true := by decide
theorem c7r525_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r525 := by
  refine ⟨c7r525targets, c7r525choice, ?_, c7r525_checked⟩
  intro S h
  simp only [c7r525targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 27 _ (by rfl)))
def c7r526 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)]
def c7r526targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
def c7r526choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r526_checked : successorFastRowCheck c7r526targets c7r526 c7r526choice = true := by decide
theorem c7r526_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r526 := by
  refine ⟨c7r526targets, c7r526choice, ?_, c7r526_checked⟩
  intro S h
  simp only [c7r526targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 3 _ (by rfl)))
def c7r527 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)]
def c7r527targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
def c7r527choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r527_checked : successorFastRowCheck c7r527targets c7r527 c7r527choice = true := by decide
theorem c7r527_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r527 := by
  refine ⟨c7r527targets, c7r527choice, ?_, c7r527_checked⟩
  intro S h
  simp only [c7r527targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 7 _ (by rfl)))
def c7r528 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)]
def c7r528targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
def c7r528choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r528_checked : successorFastRowCheck c7r528targets c7r528 c7r528choice = true := by decide
theorem c7r528_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r528 := by
  refine ⟨c7r528targets, c7r528choice, ?_, c7r528_checked⟩
  intro S h
  simp only [c7r528targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 10 _ (by rfl)))
def c7r529 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)]
def c7r529targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
def c7r529choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r529_checked : successorFastRowCheck c7r529targets c7r529 c7r529choice = true := by decide
theorem c7r529_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r529 := by
  refine ⟨c7r529targets, c7r529choice, ?_, c7r529_checked⟩
  intro S h
  simp only [c7r529targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 12 _ (by rfl)))
def c7r530 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]
def c7r530targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
def c7r530choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r530_checked : successorFastRowCheck c7r530targets c7r530 c7r530choice = true := by decide
theorem c7r530_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r530 := by
  refine ⟨c7r530targets, c7r530choice, ?_, c7r530_checked⟩
  intro S h
  simp only [c7r530targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 14 _ (by rfl)))
def c7r531 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)]
def c7r531targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r531choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r531_checked : successorFastRowCheck c7r531targets c7r531 c7r531choice = true := by decide
theorem c7r531_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r531 := by
  refine ⟨c7r531targets, c7r531choice, ?_, c7r531_checked⟩
  intro S h
  simp only [c7r531targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 17 _ (by rfl)))
def c7r532 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)]
def c7r532targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
def c7r532choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r532_checked : successorFastRowCheck c7r532targets c7r532 c7r532choice = true := by decide
theorem c7r532_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r532 := by
  refine ⟨c7r532targets, c7r532choice, ?_, c7r532_checked⟩
  intro S h
  simp only [c7r532targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 20 _ (by rfl)))
def c7r533 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]
def c7r533targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
def c7r533choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r533_checked : successorFastRowCheck c7r533targets c7r533 c7r533choice = true := by decide
theorem c7r533_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r533 := by
  refine ⟨c7r533targets, c7r533choice, ?_, c7r533_checked⟩
  intro S h
  simp only [c7r533targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 22 _ (by rfl)))
def c7r534 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)]
def c7r534targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
def c7r534choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r534_checked : successorFastRowCheck c7r534targets c7r534 c7r534choice = true := by decide
theorem c7r534_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r534 := by
  refine ⟨c7r534targets, c7r534choice, ?_, c7r534_checked⟩
  intro S h
  simp only [c7r534targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 25 _ (by rfl)))
def c7r535 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]
def c7r535targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
def c7r535choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r535_checked : successorFastRowCheck c7r535targets c7r535 c7r535choice = true := by decide
theorem c7r535_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r535 := by
  refine ⟨c7r535targets, c7r535choice, ?_, c7r535_checked⟩
  intro S h
  simp only [c7r535targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 28 _ (by rfl)))
def c7r536 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)]
def c7r536targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
def c7r536choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r536_checked : successorFastRowCheck c7r536targets c7r536 c7r536choice = true := by decide
theorem c7r536_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r536 := by
  refine ⟨c7r536targets, c7r536choice, ?_, c7r536_checked⟩
  intro S h
  simp only [c7r536targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 31 _ (by rfl)))
def c7r537 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]
def c7r537targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
def c7r537choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r537_checked : successorFastRowCheck c7r537targets c7r537 c7r537choice = true := by decide
theorem c7r537_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r537 := by
  refine ⟨c7r537targets, c7r537choice, ?_, c7r537_checked⟩
  intro S h
  simp only [c7r537targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 2 _ (by rfl)))
def c7r538 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)]
def c7r538targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
def c7r538choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r538_checked : successorFastRowCheck c7r538targets c7r538 c7r538choice = true := by decide
theorem c7r538_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r538 := by
  refine ⟨c7r538targets, c7r538choice, ?_, c7r538_checked⟩
  intro S h
  simp only [c7r538targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 7 _ (by rfl)))
def c7r539 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)]
def c7r539targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
def c7r539choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r539_checked : successorFastRowCheck c7r539targets c7r539 c7r539choice = true := by decide
theorem c7r539_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r539 := by
  refine ⟨c7r539targets, c7r539choice, ?_, c7r539_checked⟩
  intro S h
  simp only [c7r539targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 9 _ (by rfl)))
def c7r540 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]
def c7r540targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
def c7r540choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r540_checked : successorFastRowCheck c7r540targets c7r540 c7r540choice = true := by decide
theorem c7r540_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r540 := by
  refine ⟨c7r540targets, c7r540choice, ?_, c7r540_checked⟩
  intro S h
  simp only [c7r540targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 11 _ (by rfl)))
def c7r541 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)]
def c7r541targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
def c7r541choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r541_checked : successorFastRowCheck c7r541targets c7r541 c7r541choice = true := by decide
theorem c7r541_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r541 := by
  refine ⟨c7r541targets, c7r541choice, ?_, c7r541_checked⟩
  intro S h
  simp only [c7r541targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 14 _ (by rfl)))
def c7r542 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]
def c7r542targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
def c7r542choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r542_checked : successorFastRowCheck c7r542targets c7r542 c7r542choice = true := by decide
theorem c7r542_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r542 := by
  refine ⟨c7r542targets, c7r542choice, ?_, c7r542_checked⟩
  intro S h
  simp only [c7r542targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 16 _ (by rfl)))
def c7r543 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)]
def c7r543targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
def c7r543choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r543_checked : successorFastRowCheck c7r543targets c7r543 c7r543choice = true := by decide
theorem c7r543_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r543 := by
  refine ⟨c7r543targets, c7r543choice, ?_, c7r543_checked⟩
  intro S h
  simp only [c7r543targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 20 _ (by rfl)))
theorem C7R00512_closed (row : List GridPoint) (h : FamilyMember row F7B000L16) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L16, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r512_closed
  · subst row; exact c7r513_closed
  · subst row; exact c7r514_closed
  · subst row; exact c7r515_closed
  · subst row; exact c7r516_closed
  · subst row; exact c7r517_closed
  · subst row; exact c7r518_closed
  · subst row; exact c7r519_closed
  · subst row; exact c7r520_closed
  · subst row; exact c7r521_closed
  · subst row; exact c7r522_closed
  · subst row; exact c7r523_closed
  · subst row; exact c7r524_closed
  · subst row; exact c7r525_closed
  · subst row; exact c7r526_closed
  · subst row; exact c7r527_closed
  · subst row; exact c7r528_closed
  · subst row; exact c7r529_closed
  · subst row; exact c7r530_closed
  · subst row; exact c7r531_closed
  · subst row; exact c7r532_closed
  · subst row; exact c7r533_closed
  · subst row; exact c7r534_closed
  · subst row; exact c7r535_closed
  · subst row; exact c7r536_closed
  · subst row; exact c7r537_closed
  · subst row; exact c7r538_closed
  · subst row; exact c7r539_closed
  · subst row; exact c7r540_closed
  · subst row; exact c7r541_closed
  · subst row; exact c7r542_closed
  · subst row; exact c7r543_closed
end Polyomino57
