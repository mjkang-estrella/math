import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r576 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)]
def c7r576targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
def c7r576choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r576_checked : successorFastRowCheck c7r576targets c7r576 c7r576choice = true := by decide
theorem c7r576_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r576 := by
  refine ⟨c7r576targets, c7r576choice, ?_, c7r576_checked⟩
  intro S h
  simp only [c7r576targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 20 _ (by rfl)))
def c7r577 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)]
def c7r577targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
def c7r577choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r577_checked : successorFastRowCheck c7r577targets c7r577 c7r577choice = true := by decide
theorem c7r577_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r577 := by
  refine ⟨c7r577targets, c7r577choice, ?_, c7r577_checked⟩
  intro S h
  simp only [c7r577targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 23 _ (by rfl)))
def c7r578 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)]
def c7r578targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
def c7r578choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r578_checked : successorFastRowCheck c7r578targets c7r578 c7r578choice = true := by decide
theorem c7r578_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r578 := by
  refine ⟨c7r578targets, c7r578choice, ?_, c7r578_checked⟩
  intro S h
  simp only [c7r578targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 25 _ (by rfl)))
def c7r579 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]
def c7r579targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
def c7r579choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r579_checked : successorFastRowCheck c7r579targets c7r579 c7r579choice = true := by decide
theorem c7r579_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r579 := by
  refine ⟨c7r579targets, c7r579choice, ?_, c7r579_checked⟩
  intro S h
  simp only [c7r579targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 27 _ (by rfl)))
def c7r580 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)]
def c7r580targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]]
def c7r580choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r580_checked : successorFastRowCheck c7r580targets c7r580 c7r580choice = true := by decide
theorem c7r580_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r580 := by
  refine ⟨c7r580targets, c7r580choice, ?_, c7r580_checked⟩
  intro S h
  simp only [c7r580targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 30 _ (by rfl)))
def c7r581 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)]
def c7r581targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]]
def c7r581choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r581_checked : successorFastRowCheck c7r581targets c7r581 c7r581choice = true := by decide
theorem c7r581_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r581 := by
  refine ⟨c7r581targets, c7r581choice, ?_, c7r581_checked⟩
  intro S h
  simp only [c7r581targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 1 _ (by rfl)))
def c7r582 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)]
def c7r582targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]]
def c7r582choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r582_checked : successorFastRowCheck c7r582targets c7r582 c7r582choice = true := by decide
theorem c7r582_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r582 := by
  refine ⟨c7r582targets, c7r582choice, ?_, c7r582_checked⟩
  intro S h
  simp only [c7r582targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 3 _ (by rfl)))
def c7r583 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)]
def c7r583targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]]
def c7r583choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r583_checked : successorFastRowCheck c7r583targets c7r583 c7r583choice = true := by decide
theorem c7r583_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r583 := by
  refine ⟨c7r583targets, c7r583choice, ?_, c7r583_checked⟩
  intro S h
  simp only [c7r583targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 6 _ (by rfl)))
def c7r584 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)]
def c7r584targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]]
def c7r584choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r584_checked : successorFastRowCheck c7r584targets c7r584 c7r584choice = true := by decide
theorem c7r584_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r584 := by
  refine ⟨c7r584targets, c7r584choice, ?_, c7r584_checked⟩
  intro S h
  simp only [c7r584targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 9 _ (by rfl)))
def c7r585 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)]
def c7r585targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]]
def c7r585choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r585_checked : successorFastRowCheck c7r585targets c7r585 c7r585choice = true := by decide
theorem c7r585_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r585 := by
  refine ⟨c7r585targets, c7r585choice, ?_, c7r585_checked⟩
  intro S h
  simp only [c7r585targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 12 _ (by rfl)))
def c7r586 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)]
def c7r586targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]]
def c7r586choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r586_checked : successorFastRowCheck c7r586targets c7r586 c7r586choice = true := by decide
theorem c7r586_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r586 := by
  refine ⟨c7r586targets, c7r586choice, ?_, c7r586_checked⟩
  intro S h
  simp only [c7r586targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 15 _ (by rfl)))
def c7r587 : List GridPoint := [(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)]
def c7r587targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r587choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r587_checked : successorFastRowCheck c7r587targets c7r587 c7r587choice = true := by decide
theorem c7r587_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r587 := by
  refine ⟨c7r587targets, c7r587choice, ?_, c7r587_checked⟩
  intro S h
  simp only [c7r587targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 21 _ (by rfl)))
def c7r588 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)]
def c7r588targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
def c7r588choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r588_checked : successorFastRowCheck c7r588targets c7r588 c7r588choice = true := by decide
theorem c7r588_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r588 := by
  refine ⟨c7r588targets, c7r588choice, ?_, c7r588_checked⟩
  intro S h
  simp only [c7r588targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 27 _ (by rfl)))
def c7r589 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)]
def c7r589targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r589choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r589_checked : successorFastRowCheck c7r589targets c7r589 c7r589choice = true := by decide
theorem c7r589_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r589 := by
  refine ⟨c7r589targets, c7r589choice, ?_, c7r589_checked⟩
  intro S h
  simp only [c7r589targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 0 _ (by rfl)))
def c7r590 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)]
def c7r590targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
def c7r590choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r590_checked : successorFastRowCheck c7r590targets c7r590 c7r590choice = true := by decide
theorem c7r590_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r590 := by
  refine ⟨c7r590targets, c7r590choice, ?_, c7r590_checked⟩
  intro S h
  simp only [c7r590targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 2 _ (by rfl)))
def c7r591 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)]
def c7r591targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
def c7r591choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r591_checked : successorFastRowCheck c7r591targets c7r591 c7r591choice = true := by decide
theorem c7r591_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r591 := by
  refine ⟨c7r591targets, c7r591choice, ?_, c7r591_checked⟩
  intro S h
  simp only [c7r591targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 4 _ (by rfl)))
def c7r592 : List GridPoint := [(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)]
def c7r592targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
def c7r592choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r592_checked : successorFastRowCheck c7r592targets c7r592 c7r592choice = true := by decide
theorem c7r592_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r592 := by
  refine ⟨c7r592targets, c7r592choice, ?_, c7r592_checked⟩
  intro S h
  simp only [c7r592targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 8 _ (by rfl)))
def c7r593 : List GridPoint := [(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)]
def c7r593targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
def c7r593choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r593_checked : successorFastRowCheck c7r593targets c7r593 c7r593choice = true := by decide
theorem c7r593_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r593 := by
  refine ⟨c7r593targets, c7r593choice, ?_, c7r593_checked⟩
  intro S h
  simp only [c7r593targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 16 _ (by rfl)))
def c7r594 : List GridPoint := [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)]
def c7r594targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r594choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r594_checked : successorFastRowCheck c7r594targets c7r594 c7r594choice = true := by decide
theorem c7r594_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r594 := by
  refine ⟨c7r594targets, c7r594choice, ?_, c7r594_checked⟩
  intro S h
  simp only [c7r594targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 23 _ (by rfl)))
def c7r595 : List GridPoint := [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)]
def c7r595targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r595choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r595_checked : successorFastRowCheck c7r595targets c7r595 c7r595choice = true := by decide
theorem c7r595_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r595 := by
  refine ⟨c7r595targets, c7r595choice, ?_, c7r595_checked⟩
  intro S h
  simp only [c7r595targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 26 _ (by rfl)))
def c7r596 : List GridPoint := [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)]
def c7r596targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r596choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r596_checked : successorFastRowCheck c7r596targets c7r596 c7r596choice = true := by decide
theorem c7r596_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r596 := by
  refine ⟨c7r596targets, c7r596choice, ?_, c7r596_checked⟩
  intro S h
  simp only [c7r596targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 28 _ (by rfl)))
def c7r597 : List GridPoint := [(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)]
def c7r597targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r597choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r597_checked : successorFastRowCheck c7r597targets c7r597 c7r597choice = true := by decide
theorem c7r597_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r597 := by
  refine ⟨c7r597targets, c7r597choice, ?_, c7r597_checked⟩
  intro S h
  simp only [c7r597targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 30 _ (by rfl)))
def c7r598 : List GridPoint := [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)]
def c7r598targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r598choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r598_checked : successorFastRowCheck c7r598targets c7r598 c7r598choice = true := by decide
theorem c7r598_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r598 := by
  refine ⟨c7r598targets, c7r598choice, ?_, c7r598_checked⟩
  intro S h
  simp only [c7r598targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 3 _ (by rfl)))
def c7r599 : List GridPoint := [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)]
def c7r599targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]]
def c7r599choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r599_checked : successorFastRowCheck c7r599targets c7r599 c7r599choice = true := by decide
theorem c7r599_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r599 := by
  refine ⟨c7r599targets, c7r599choice, ?_, c7r599_checked⟩
  intro S h
  simp only [c7r599targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 9 _ (by rfl)))
def c7r600 : List GridPoint := [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)]
def c7r600targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r600choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,1),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r600_checked : successorFastRowCheck c7r600targets c7r600 c7r600choice = true := by decide
theorem c7r600_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r600 := by
  refine ⟨c7r600targets, c7r600choice, ?_, c7r600_checked⟩
  intro S h
  simp only [c7r600targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 17 _ (by rfl)))
def c7r601 : List GridPoint := [(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r601targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r601choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r601_checked : successorFastRowCheck c7r601targets c7r601 c7r601choice = true := by decide
theorem c7r601_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r601 := by
  refine ⟨c7r601targets, c7r601choice, ?_, c7r601_checked⟩
  intro S h
  simp only [c7r601targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 27 _ (by rfl)))
def c7r602 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def c7r602targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
def c7r602choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,6),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r602_checked : successorFastRowCheck c7r602targets c7r602 c7r602choice = true := by decide
theorem c7r602_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r602 := by
  refine ⟨c7r602targets, c7r602choice, ?_, c7r602_checked⟩
  intro S h
  simp only [c7r602targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 5 _ (by rfl)))
def c7r603 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def c7r603targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
def c7r603choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r603_checked : successorFastRowCheck c7r603targets c7r603 c7r603choice = true := by decide
theorem c7r603_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r603 := by
  refine ⟨c7r603targets, c7r603choice, ?_, c7r603_checked⟩
  intro S h
  simp only [c7r603targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 10 _ (by rfl)))
def c7r604 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def c7r604targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
def c7r604choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r604_checked : successorFastRowCheck c7r604targets c7r604 c7r604choice = true := by decide
theorem c7r604_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r604 := by
  refine ⟨c7r604targets, c7r604choice, ?_, c7r604_checked⟩
  intro S h
  simp only [c7r604targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 14 _ (by rfl)))
def c7r605 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def c7r605targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
def c7r605choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r605_checked : successorFastRowCheck c7r605targets c7r605 c7r605choice = true := by decide
theorem c7r605_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r605 := by
  refine ⟨c7r605targets, c7r605choice, ?_, c7r605_checked⟩
  intro S h
  simp only [c7r605targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 17 _ (by rfl)))
def c7r606 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def c7r606targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
def c7r606choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r606_checked : successorFastRowCheck c7r606targets c7r606 c7r606choice = true := by decide
theorem c7r606_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r606 := by
  refine ⟨c7r606targets, c7r606choice, ?_, c7r606_checked⟩
  intro S h
  simp only [c7r606targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 19 _ (by rfl)))
def c7r607 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def c7r607targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
def c7r607choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r607_checked : successorFastRowCheck c7r607targets c7r607 c7r607choice = true := by decide
theorem c7r607_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r607 := by
  refine ⟨c7r607targets, c7r607choice, ?_, c7r607_checked⟩
  intro S h
  simp only [c7r607targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 21 _ (by rfl)))
theorem C7R00576_closed (row : List GridPoint) (h : FamilyMember row F7B000L18) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L18, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r576_closed
  · subst row; exact c7r577_closed
  · subst row; exact c7r578_closed
  · subst row; exact c7r579_closed
  · subst row; exact c7r580_closed
  · subst row; exact c7r581_closed
  · subst row; exact c7r582_closed
  · subst row; exact c7r583_closed
  · subst row; exact c7r584_closed
  · subst row; exact c7r585_closed
  · subst row; exact c7r586_closed
  · subst row; exact c7r587_closed
  · subst row; exact c7r588_closed
  · subst row; exact c7r589_closed
  · subst row; exact c7r590_closed
  · subst row; exact c7r591_closed
  · subst row; exact c7r592_closed
  · subst row; exact c7r593_closed
  · subst row; exact c7r594_closed
  · subst row; exact c7r595_closed
  · subst row; exact c7r596_closed
  · subst row; exact c7r597_closed
  · subst row; exact c7r598_closed
  · subst row; exact c7r599_closed
  · subst row; exact c7r600_closed
  · subst row; exact c7r601_closed
  · subst row; exact c7r602_closed
  · subst row; exact c7r603_closed
  · subst row; exact c7r604_closed
  · subst row; exact c7r605_closed
  · subst row; exact c7r606_closed
  · subst row; exact c7r607_closed
end Polyomino57
