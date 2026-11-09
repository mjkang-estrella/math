import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r128 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3)]
def c7r128targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
def c7r128choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r128_checked : successorFastRowCheck c7r128targets c7r128 c7r128choice = true := by decide
theorem c7r128_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r128 := by
  refine ⟨c7r128targets, c7r128choice, ?_, c7r128_checked⟩
  intro S h
  simp only [c7r128targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 11 _ (by rfl)))
def c7r129 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1)]
def c7r129targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]]
def c7r129choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r129_checked : successorFastRowCheck c7r129targets c7r129 c7r129choice = true := by decide
theorem c7r129_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r129 := by
  refine ⟨c7r129targets, c7r129choice, ?_, c7r129_checked⟩
  intro S h
  simp only [c7r129targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 14 _ (by rfl)))
def c7r130 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2)]
def c7r130targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]]
def c7r130choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r130_checked : successorFastRowCheck c7r130targets c7r130 c7r130choice = true := by decide
theorem c7r130_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r130 := by
  refine ⟨c7r130targets, c7r130choice, ?_, c7r130_checked⟩
  intro S h
  simp only [c7r130targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 17 _ (by rfl)))
def c7r131 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0)]
def c7r131targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]]
def c7r131choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r131_checked : successorFastRowCheck c7r131targets c7r131 c7r131choice = true := by decide
theorem c7r131_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r131 := by
  refine ⟨c7r131targets, c7r131choice, ?_, c7r131_checked⟩
  intro S h
  simp only [c7r131targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 19 _ (by rfl)))
def c7r132 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2)]
def c7r132targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]]
def c7r132choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r132_checked : successorFastRowCheck c7r132targets c7r132 c7r132choice = true := by decide
theorem c7r132_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r132 := by
  refine ⟨c7r132targets, c7r132choice, ?_, c7r132_checked⟩
  intro S h
  simp only [c7r132targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 22 _ (by rfl)))
def c7r133 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1)]
def c7r133targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]]
def c7r133choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r133_checked : successorFastRowCheck c7r133targets c7r133 c7r133choice = true := by decide
theorem c7r133_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r133 := by
  refine ⟨c7r133targets, c7r133choice, ?_, c7r133_checked⟩
  intro S h
  simp only [c7r133targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 25 _ (by rfl)))
def c7r134 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3)]
def c7r134targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]]
def c7r134choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r134_checked : successorFastRowCheck c7r134targets c7r134 c7r134choice = true := by decide
theorem c7r134_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r134 := by
  refine ⟨c7r134targets, c7r134choice, ?_, c7r134_checked⟩
  intro S h
  simp only [c7r134targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 28 _ (by rfl)))
def c7r135 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2)]
def c7r135targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]]
def c7r135choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r135_checked : successorFastRowCheck c7r135targets c7r135 c7r135choice = true := by decide
theorem c7r135_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r135 := by
  refine ⟨c7r135targets, c7r135choice, ?_, c7r135_checked⟩
  intro S h
  simp only [c7r135targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 31 _ (by rfl)))
def c7r136 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2)]
def c7r136targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)]]
def c7r136choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r136_checked : successorFastRowCheck c7r136targets c7r136 c7r136choice = true := by decide
theorem c7r136_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r136 := by
  refine ⟨c7r136targets, c7r136choice, ?_, c7r136_checked⟩
  intro S h
  simp only [c7r136targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 4 _ (by rfl)))
def c7r137 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0)]
def c7r137targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)]]
def c7r137choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r137_checked : successorFastRowCheck c7r137targets c7r137 c7r137choice = true := by decide
theorem c7r137_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r137 := by
  refine ⟨c7r137targets, c7r137choice, ?_, c7r137_checked⟩
  intro S h
  simp only [c7r137targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 6 _ (by rfl)))
def c7r138 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1)]
def c7r138targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]]
def c7r138choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r138_checked : successorFastRowCheck c7r138targets c7r138 c7r138choice = true := by decide
theorem c7r138_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r138 := by
  refine ⟨c7r138targets, c7r138choice, ?_, c7r138_checked⟩
  intro S h
  simp only [c7r138targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 8 _ (by rfl)))
def c7r139 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1)]
def c7r139targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)]]
def c7r139choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r139_checked : successorFastRowCheck c7r139targets c7r139 c7r139choice = true := by decide
theorem c7r139_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r139 := by
  refine ⟨c7r139targets, c7r139choice, ?_, c7r139_checked⟩
  intro S h
  simp only [c7r139targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 11 _ (by rfl)))
def c7r140 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0)]
def c7r140targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)]]
def c7r140choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r140_checked : successorFastRowCheck c7r140targets c7r140 c7r140choice = true := by decide
theorem c7r140_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r140 := by
  refine ⟨c7r140targets, c7r140choice, ?_, c7r140_checked⟩
  intro S h
  simp only [c7r140targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 13 _ (by rfl)))
def c7r141 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3)]
def c7r141targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)]]
def c7r141choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r141_checked : successorFastRowCheck c7r141targets c7r141 c7r141choice = true := by decide
theorem c7r141_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r141 := by
  refine ⟨c7r141targets, c7r141choice, ?_, c7r141_checked⟩
  intro S h
  simp only [c7r141targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 17 _ (by rfl)))
def c7r142 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1)]
def c7r142targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)]]
def c7r142choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r142_checked : successorFastRowCheck c7r142targets c7r142 c7r142choice = true := by decide
theorem c7r142_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r142 := by
  refine ⟨c7r142targets, c7r142choice, ?_, c7r142_checked⟩
  intro S h
  simp only [c7r142targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 20 _ (by rfl)))
def c7r143 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2)]
def c7r143targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]]
def c7r143choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r143_checked : successorFastRowCheck c7r143targets c7r143 c7r143choice = true := by decide
theorem c7r143_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r143 := by
  refine ⟨c7r143targets, c7r143choice, ?_, c7r143_checked⟩
  intro S h
  simp only [c7r143targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 22 _ (by rfl)))
def c7r144 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1)]
def c7r144targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)]]
def c7r144choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r144_checked : successorFastRowCheck c7r144targets c7r144 c7r144choice = true := by decide
theorem c7r144_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r144 := by
  refine ⟨c7r144targets, c7r144choice, ?_, c7r144_checked⟩
  intro S h
  simp only [c7r144targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 25 _ (by rfl)))
def c7r145 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2)]
def c7r145targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)]]
def c7r145choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r145_checked : successorFastRowCheck c7r145targets c7r145 c7r145choice = true := by decide
theorem c7r145_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r145 := by
  refine ⟨c7r145targets, c7r145choice, ?_, c7r145_checked⟩
  intro S h
  simp only [c7r145targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 28 _ (by rfl)))
def c7r146 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1)]
def c7r146targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]]
def c7r146choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r146_checked : successorFastRowCheck c7r146targets c7r146 c7r146choice = true := by decide
theorem c7r146_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r146 := by
  refine ⟨c7r146targets, c7r146choice, ?_, c7r146_checked⟩
  intro S h
  simp only [c7r146targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 31 _ (by rfl)))
def c7r147 : List GridPoint := [(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2)]
def c7r147targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r147choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r147_checked : successorFastRowCheck c7r147targets c7r147 c7r147choice = true := by decide
theorem c7r147_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r147 := by
  refine ⟨c7r147targets, c7r147choice, ?_, c7r147_checked⟩
  intro S h
  simp only [c7r147targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 4 _ (by rfl)))
def c7r148 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3)]
def c7r148targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r148choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r148_checked : successorFastRowCheck c7r148targets c7r148 c7r148choice = true := by decide
theorem c7r148_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r148 := by
  refine ⟨c7r148targets, c7r148choice, ?_, c7r148_checked⟩
  intro S h
  simp only [c7r148targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 10 _ (by rfl)))
def c7r149 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0)]
def c7r149targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r149choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r149_checked : successorFastRowCheck c7r149targets c7r149 c7r149choice = true := by decide
theorem c7r149_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r149 := by
  refine ⟨c7r149targets, c7r149choice, ?_, c7r149_checked⟩
  intro S h
  simp only [c7r149targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 13 _ (by rfl)))
def c7r150 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1)]
def c7r150targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r150choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r150_checked : successorFastRowCheck c7r150targets c7r150 c7r150choice = true := by decide
theorem c7r150_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r150 := by
  refine ⟨c7r150targets, c7r150choice, ?_, c7r150_checked⟩
  intro S h
  simp only [c7r150targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 15 _ (by rfl)))
def c7r151 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2)]
def c7r151targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r151choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r151_checked : successorFastRowCheck c7r151targets c7r151 c7r151choice = true := by decide
theorem c7r151_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r151 := by
  refine ⟨c7r151targets, c7r151choice, ?_, c7r151_checked⟩
  intro S h
  simp only [c7r151targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 17 _ (by rfl)))
def c7r152 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1)]
def c7r152targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)]]
def c7r152choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r152_checked : successorFastRowCheck c7r152targets c7r152 c7r152choice = true := by decide
theorem c7r152_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r152 := by
  refine ⟨c7r152targets, c7r152choice, ?_, c7r152_checked⟩
  intro S h
  simp only [c7r152targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 20 _ (by rfl)))
def c7r153 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0)]
def c7r153targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)]]
def c7r153choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r153_checked : successorFastRowCheck c7r153targets c7r153 c7r153choice = true := by decide
theorem c7r153_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r153 := by
  refine ⟨c7r153targets, c7r153choice, ?_, c7r153_checked⟩
  intro S h
  simp only [c7r153targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 22 _ (by rfl)))
def c7r154 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2)]
def c7r154targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)]]
def c7r154choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r154_checked : successorFastRowCheck c7r154targets c7r154 c7r154choice = true := by decide
theorem c7r154_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r154 := by
  refine ⟨c7r154targets, c7r154choice, ?_, c7r154_checked⟩
  intro S h
  simp only [c7r154targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 25 _ (by rfl)))
def c7r155 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1)]
def c7r155targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)]]
def c7r155choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r155_checked : successorFastRowCheck c7r155targets c7r155 c7r155choice = true := by decide
theorem c7r155_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r155 := by
  refine ⟨c7r155targets, c7r155choice, ?_, c7r155_checked⟩
  intro S h
  simp only [c7r155targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 28 _ (by rfl)))
def c7r156 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2)]
def c7r156targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)]]
def c7r156choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r156_checked : successorFastRowCheck c7r156targets c7r156 c7r156choice = true := by decide
theorem c7r156_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r156 := by
  refine ⟨c7r156targets, c7r156choice, ?_, c7r156_checked⟩
  intro S h
  simp only [c7r156targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 1 _ (by rfl)))
def c7r157 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0)]
def c7r157targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)]]
def c7r157choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r157_checked : successorFastRowCheck c7r157targets c7r157 c7r157choice = true := by decide
theorem c7r157_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r157 := by
  refine ⟨c7r157targets, c7r157choice, ?_, c7r157_checked⟩
  intro S h
  simp only [c7r157targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 3 _ (by rfl)))
def c7r158 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1)]
def c7r158targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)]]
def c7r158choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r158_checked : successorFastRowCheck c7r158targets c7r158 c7r158choice = true := by decide
theorem c7r158_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r158 := by
  refine ⟨c7r158targets, c7r158choice, ?_, c7r158_checked⟩
  intro S h
  simp only [c7r158targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 5 _ (by rfl)))
def c7r159 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1)]
def c7r159targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)]]
def c7r159choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r159_checked : successorFastRowCheck c7r159targets c7r159 c7r159choice = true := by decide
theorem c7r159_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r159 := by
  refine ⟨c7r159targets, c7r159choice, ?_, c7r159_checked⟩
  intro S h
  simp only [c7r159targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 8 _ (by rfl)))
theorem C7R00128_closed (row : List GridPoint) (h : FamilyMember row F7B000L4) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L4, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r128_closed
  · subst row; exact c7r129_closed
  · subst row; exact c7r130_closed
  · subst row; exact c7r131_closed
  · subst row; exact c7r132_closed
  · subst row; exact c7r133_closed
  · subst row; exact c7r134_closed
  · subst row; exact c7r135_closed
  · subst row; exact c7r136_closed
  · subst row; exact c7r137_closed
  · subst row; exact c7r138_closed
  · subst row; exact c7r139_closed
  · subst row; exact c7r140_closed
  · subst row; exact c7r141_closed
  · subst row; exact c7r142_closed
  · subst row; exact c7r143_closed
  · subst row; exact c7r144_closed
  · subst row; exact c7r145_closed
  · subst row; exact c7r146_closed
  · subst row; exact c7r147_closed
  · subst row; exact c7r148_closed
  · subst row; exact c7r149_closed
  · subst row; exact c7r150_closed
  · subst row; exact c7r151_closed
  · subst row; exact c7r152_closed
  · subst row; exact c7r153_closed
  · subst row; exact c7r154_closed
  · subst row; exact c7r155_closed
  · subst row; exact c7r156_closed
  · subst row; exact c7r157_closed
  · subst row; exact c7r158_closed
  · subst row; exact c7r159_closed
end Polyomino57
