import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r96 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2)]
def c7r96targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2)]]
def c7r96choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r96_checked : successorFastRowCheck c7r96targets c7r96 c7r96choice = true := by decide
theorem c7r96_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r96 := by
  refine ⟨c7r96targets, c7r96choice, ?_, c7r96_checked⟩
  intro S h
  simp only [c7r96targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 24 _ (by rfl)))
def c7r97 : List GridPoint := [(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1)]
def c7r97targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1)]]
def c7r97choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r97_checked : successorFastRowCheck c7r97targets c7r97 c7r97choice = true := by decide
theorem c7r97_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r97 := by
  refine ⟨c7r97targets, c7r97choice, ?_, c7r97_checked⟩
  intro S h
  simp only [c7r97targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 27 _ (by rfl)))
def c7r98 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5)]
def c7r98targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,5)]]
def c7r98choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,6),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r98_checked : successorFastRowCheck c7r98targets c7r98 c7r98choice = true := by decide
theorem c7r98_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r98 := by
  refine ⟨c7r98targets, c7r98choice, ?_, c7r98_checked⟩
  intro S h
  simp only [c7r98targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 0 _ (by rfl)))
def c7r99 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2)]
def c7r99targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2)]]
def c7r99choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r99_checked : successorFastRowCheck c7r99targets c7r99 c7r99choice = true := by decide
theorem c7r99_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r99 := by
  refine ⟨c7r99targets, c7r99choice, ?_, c7r99_checked⟩
  intro S h
  simp only [c7r99targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 4 _ (by rfl)))
def c7r100 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3)]
def c7r100targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3)]]
def c7r100choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r100_checked : successorFastRowCheck c7r100targets c7r100 c7r100choice = true := by decide
theorem c7r100_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r100 := by
  refine ⟨c7r100targets, c7r100choice, ?_, c7r100_checked⟩
  intro S h
  simp only [c7r100targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 6 _ (by rfl)))
def c7r101 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4)]
def c7r101targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,4)]]
def c7r101choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,5),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r101_checked : successorFastRowCheck c7r101targets c7r101 c7r101choice = true := by decide
theorem c7r101_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r101 := by
  refine ⟨c7r101targets, c7r101choice, ?_, c7r101_checked⟩
  intro S h
  simp only [c7r101targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 8 _ (by rfl)))
def c7r102 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2)]
def c7r102targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2)]]
def c7r102choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r102_checked : successorFastRowCheck c7r102targets c7r102 c7r102choice = true := by decide
theorem c7r102_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r102 := by
  refine ⟨c7r102targets, c7r102choice, ?_, c7r102_checked⟩
  intro S h
  simp only [c7r102targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 12 _ (by rfl)))
def c7r103 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3)]
def c7r103targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3)]]
def c7r103choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r103_checked : successorFastRowCheck c7r103targets c7r103 c7r103choice = true := by decide
theorem c7r103_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r103 := by
  refine ⟨c7r103targets, c7r103choice, ?_, c7r103_checked⟩
  intro S h
  simp only [c7r103targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 15 _ (by rfl)))
def c7r104 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2)]
def c7r104targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2)]]
def c7r104choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r104_checked : successorFastRowCheck c7r104targets c7r104 c7r104choice = true := by decide
theorem c7r104_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r104 := by
  refine ⟨c7r104targets, c7r104choice, ?_, c7r104_checked⟩
  intro S h
  simp only [c7r104targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 18 _ (by rfl)))
def c7r105 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4)]
def c7r105targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4)]]
def c7r105choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r105_checked : successorFastRowCheck c7r105targets c7r105 c7r105choice = true := by decide
theorem c7r105_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r105 := by
  refine ⟨c7r105targets, c7r105choice, ?_, c7r105_checked⟩
  intro S h
  simp only [c7r105targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 21 _ (by rfl)))
def c7r106 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3)]
def c7r106targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,3)]]
def c7r106choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r106_checked : successorFastRowCheck c7r106targets c7r106 c7r106choice = true := by decide
theorem c7r106_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r106 := by
  refine ⟨c7r106targets, c7r106choice, ?_, c7r106_checked⟩
  intro S h
  simp only [c7r106targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 24 _ (by rfl)))
def c7r107 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2)]
def c7r107targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r107choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r107_checked : successorFastRowCheck c7r107targets c7r107 c7r107choice = true := by decide
theorem c7r107_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r107 := by
  refine ⟨c7r107targets, c7r107choice, ?_, c7r107_checked⟩
  intro S h
  simp only [c7r107targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 29 _ (by rfl)))
def c7r108 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3)]
def c7r108targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3)]]
def c7r108choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r108_checked : successorFastRowCheck c7r108targets c7r108 c7r108choice = true := by decide
theorem c7r108_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r108 := by
  refine ⟨c7r108targets, c7r108choice, ?_, c7r108_checked⟩
  intro S h
  simp only [c7r108targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 1 _ (by rfl)))
def c7r109 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1)]
def c7r109targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1)]]
def c7r109choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r109_checked : successorFastRowCheck c7r109targets c7r109 c7r109choice = true := by decide
theorem c7r109_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r109 := by
  refine ⟨c7r109targets, c7r109choice, ?_, c7r109_checked⟩
  intro S h
  simp only [c7r109targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 4 _ (by rfl)))
def c7r110 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2)]
def c7r110targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2)]]
def c7r110choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r110_checked : successorFastRowCheck c7r110targets c7r110 c7r110choice = true := by decide
theorem c7r110_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r110 := by
  refine ⟨c7r110targets, c7r110choice, ?_, c7r110_checked⟩
  intro S h
  simp only [c7r110targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 6 _ (by rfl)))
def c7r111 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4)]
def c7r111targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4)]]
def c7r111choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,5),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r111_checked : successorFastRowCheck c7r111targets c7r111 c7r111choice = true := by decide
theorem c7r111_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r111 := by
  refine ⟨c7r111targets, c7r111choice, ?_, c7r111_checked⟩
  intro S h
  simp only [c7r111targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 10 _ (by rfl)))
def c7r112 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2)]
def c7r112targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2)]]
def c7r112choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r112_checked : successorFastRowCheck c7r112targets c7r112 c7r112choice = true := by decide
theorem c7r112_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r112 := by
  refine ⟨c7r112targets, c7r112choice, ?_, c7r112_checked⟩
  intro S h
  simp only [c7r112targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 13 _ (by rfl)))
def c7r113 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3)]
def c7r113targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,3)]]
def c7r113choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r113_checked : successorFastRowCheck c7r113targets c7r113 c7r113choice = true := by decide
theorem c7r113_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r113 := by
  refine ⟨c7r113targets, c7r113choice, ?_, c7r113_checked⟩
  intro S h
  simp only [c7r113targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 15 _ (by rfl)))
def c7r114 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2)]
def c7r114targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2)]]
def c7r114choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r114_checked : successorFastRowCheck c7r114targets c7r114 c7r114choice = true := by decide
theorem c7r114_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r114 := by
  refine ⟨c7r114targets, c7r114choice, ?_, c7r114_checked⟩
  intro S h
  simp only [c7r114targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 19 _ (by rfl)))
def c7r115 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3)]
def c7r115targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3)]]
def c7r115choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,4),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r115_checked : successorFastRowCheck c7r115targets c7r115 c7r115choice = true := by decide
theorem c7r115_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r115 := by
  refine ⟨c7r115targets, c7r115choice, ?_, c7r115_checked⟩
  intro S h
  simp only [c7r115targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 22 _ (by rfl)))
def c7r116 : List GridPoint := [(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2)]
def c7r116targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2)]]
def c7r116choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((0,-1),(3,(0,1))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0))),((4,3),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r116_checked : successorFastRowCheck c7r116targets c7r116 c7r116choice = true := by decide
theorem c7r116_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r116 := by
  refine ⟨c7r116targets, c7r116choice, ?_, c7r116_checked⟩
  intro S h
  simp only [c7r116targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 25 _ (by rfl)))
def c7r117 : List GridPoint := [(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3)]
def c7r117targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)]]
def c7r117choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,4),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r117_checked : successorFastRowCheck c7r117targets c7r117 c7r117choice = true := by decide
theorem c7r117_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r117 := by
  refine ⟨c7r117targets, c7r117choice, ?_, c7r117_checked⟩
  intro S h
  simp only [c7r117targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 31 _ (by rfl)))
def c7r118 : List GridPoint := [(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3)]
def c7r118targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]]
def c7r118choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r118_checked : successorFastRowCheck c7r118targets c7r118 c7r118choice = true := by decide
theorem c7r118_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r118 := by
  refine ⟨c7r118targets, c7r118choice, ?_, c7r118_checked⟩
  intro S h
  simp only [c7r118targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 4 _ (by rfl)))
def c7r119 : List GridPoint := [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4)]
def c7r119targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r119choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r119_checked : successorFastRowCheck c7r119targets c7r119 c7r119choice = true := by decide
theorem c7r119_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r119 := by
  refine ⟨c7r119targets, c7r119choice, ?_, c7r119_checked⟩
  intro S h
  simp only [c7r119targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 9 _ (by rfl)))
def c7r120 : List GridPoint := [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1)]
def c7r120targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)]]
def c7r120choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r120_checked : successorFastRowCheck c7r120targets c7r120 c7r120choice = true := by decide
theorem c7r120_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r120 := by
  refine ⟨c7r120targets, c7r120choice, ?_, c7r120_checked⟩
  intro S h
  simp only [c7r120targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 13 _ (by rfl)))
def c7r121 : List GridPoint := [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2)]
def c7r121targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)]]
def c7r121choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r121_checked : successorFastRowCheck c7r121targets c7r121 c7r121choice = true := by decide
theorem c7r121_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r121 := by
  refine ⟨c7r121targets, c7r121choice, ?_, c7r121_checked⟩
  intro S h
  simp only [c7r121targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 15 _ (by rfl)))
def c7r122 : List GridPoint := [(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3)]
def c7r122targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)]]
def c7r122choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,4),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r122_checked : successorFastRowCheck c7r122targets c7r122 c7r122choice = true := by decide
theorem c7r122_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r122 := by
  refine ⟨c7r122targets, c7r122choice, ?_, c7r122_checked⟩
  intro S h
  simp only [c7r122targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 17 _ (by rfl)))
def c7r123 : List GridPoint := [(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4)]
def c7r123targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r123choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r123_checked : successorFastRowCheck c7r123targets c7r123 c7r123choice = true := by decide
theorem c7r123_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r123 := by
  refine ⟨c7r123targets, c7r123choice, ?_, c7r123_checked⟩
  intro S h
  simp only [c7r123targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L5_lift _ (familyLookup_sound F8B000L5 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 25 _ (by rfl)))
def c7r124 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r124targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r124choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r124_checked : successorFastRowCheck c7r124targets c7r124 c7r124choice = true := by decide
theorem c7r124_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r124 := by
  refine ⟨c7r124targets, c7r124choice, ?_, c7r124_checked⟩
  intro S h
  simp only [c7r124targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 0 _ (by rfl)))
def c7r125 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0)]
def c7r125targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
def c7r125choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r125_checked : successorFastRowCheck c7r125targets c7r125 c7r125choice = true := by decide
theorem c7r125_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r125 := by
  refine ⟨c7r125targets, c7r125choice, ?_, c7r125_checked⟩
  intro S h
  simp only [c7r125targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 4 _ (by rfl)))
def c7r126 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1)]
def c7r126targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
def c7r126choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r126_checked : successorFastRowCheck c7r126targets c7r126 c7r126choice = true := by decide
theorem c7r126_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r126 := by
  refine ⟨c7r126targets, c7r126choice, ?_, c7r126_checked⟩
  intro S h
  simp only [c7r126targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 7 _ (by rfl)))
def c7r127 : List GridPoint := [(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2)]
def c7r127targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
def c7r127choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r127_checked : successorFastRowCheck c7r127targets c7r127 c7r127choice = true := by decide
theorem c7r127_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r127 := by
  refine ⟨c7r127targets, c7r127choice, ?_, c7r127_checked⟩
  intro S h
  simp only [c7r127targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 9 _ (by rfl)))
theorem C7R00096_closed (row : List GridPoint) (h : FamilyMember row F7B000L3) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L3, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r96_closed
  · subst row; exact c7r97_closed
  · subst row; exact c7r98_closed
  · subst row; exact c7r99_closed
  · subst row; exact c7r100_closed
  · subst row; exact c7r101_closed
  · subst row; exact c7r102_closed
  · subst row; exact c7r103_closed
  · subst row; exact c7r104_closed
  · subst row; exact c7r105_closed
  · subst row; exact c7r106_closed
  · subst row; exact c7r107_closed
  · subst row; exact c7r108_closed
  · subst row; exact c7r109_closed
  · subst row; exact c7r110_closed
  · subst row; exact c7r111_closed
  · subst row; exact c7r112_closed
  · subst row; exact c7r113_closed
  · subst row; exact c7r114_closed
  · subst row; exact c7r115_closed
  · subst row; exact c7r116_closed
  · subst row; exact c7r117_closed
  · subst row; exact c7r118_closed
  · subst row; exact c7r119_closed
  · subst row; exact c7r120_closed
  · subst row; exact c7r121_closed
  · subst row; exact c7r122_closed
  · subst row; exact c7r123_closed
  · subst row; exact c7r124_closed
  · subst row; exact c7r125_closed
  · subst row; exact c7r126_closed
  · subst row; exact c7r127_closed
end Polyomino57
