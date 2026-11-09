import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r736 : List GridPoint := [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]
def c7r736targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r736choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r736_checked : successorFastRowCheck c7r736targets c7r736 c7r736choice = true := by decide
theorem c7r736_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r736 := by
  refine ⟨c7r736targets, c7r736choice, ?_, c7r736_checked⟩
  intro S h
  simp only [c7r736targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 6 _ (by rfl)))
def c7r737 : List GridPoint := [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)]
def c7r737targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r737choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,1),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r737_checked : successorFastRowCheck c7r737targets c7r737 c7r737choice = true := by decide
theorem c7r737_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r737 := by
  refine ⟨c7r737targets, c7r737choice, ?_, c7r737_checked⟩
  intro S h
  simp only [c7r737targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 11 _ (by rfl)))
def c7r738 : List GridPoint := [(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)]
def c7r738targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)]]
def c7r738choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,1),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r738_checked : successorFastRowCheck c7r738targets c7r738 c7r738choice = true := by decide
theorem c7r738_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r738 := by
  refine ⟨c7r738targets, c7r738choice, ?_, c7r738_checked⟩
  intro S h
  simp only [c7r738targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 17 _ (by rfl)))
def c7r739 : List GridPoint := [(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)]
def c7r739targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r739choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r739_checked : successorFastRowCheck c7r739targets c7r739 c7r739choice = true := by decide
theorem c7r739_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r739 := by
  refine ⟨c7r739targets, c7r739choice, ?_, c7r739_checked⟩
  intro S h
  simp only [c7r739targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 26 _ (by rfl)))
def c7r740 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)]
def c7r740targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
def c7r740choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,5),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r740_checked : successorFastRowCheck c7r740targets c7r740 c7r740choice = true := by decide
theorem c7r740_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r740 := by
  refine ⟨c7r740targets, c7r740choice, ?_, c7r740_checked⟩
  intro S h
  simp only [c7r740targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 3 _ (by rfl)))
def c7r741 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)]
def c7r741targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
def c7r741choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r741_checked : successorFastRowCheck c7r741targets c7r741 c7r741choice = true := by decide
theorem c7r741_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r741 := by
  refine ⟨c7r741targets, c7r741choice, ?_, c7r741_checked⟩
  intro S h
  simp only [c7r741targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 7 _ (by rfl)))
def c7r742 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)]
def c7r742targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
def c7r742choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r742_checked : successorFastRowCheck c7r742targets c7r742 c7r742choice = true := by decide
theorem c7r742_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r742 := by
  refine ⟨c7r742targets, c7r742choice, ?_, c7r742_checked⟩
  intro S h
  simp only [c7r742targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 10 _ (by rfl)))
def c7r743 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)]
def c7r743targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
def c7r743choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r743_checked : successorFastRowCheck c7r743targets c7r743 c7r743choice = true := by decide
theorem c7r743_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r743 := by
  refine ⟨c7r743targets, c7r743choice, ?_, c7r743_checked⟩
  intro S h
  simp only [c7r743targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 12 _ (by rfl)))
def c7r744 : List GridPoint := [(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]
def c7r744targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
def c7r744choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r744_checked : successorFastRowCheck c7r744targets c7r744 c7r744choice = true := by decide
theorem c7r744_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r744 := by
  refine ⟨c7r744targets, c7r744choice, ?_, c7r744_checked⟩
  intro S h
  simp only [c7r744targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 14 _ (by rfl)))
def c7r745 : List GridPoint := [(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)]
def c7r745targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
def c7r745choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,1),(3,(0,0))),((1,2),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r745_checked : successorFastRowCheck c7r745targets c7r745 c7r745choice = true := by decide
theorem c7r745_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r745 := by
  refine ⟨c7r745targets, c7r745choice, ?_, c7r745_checked⟩
  intro S h
  simp only [c7r745targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 22 _ (by rfl)))
def c7r746 : List GridPoint := [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)]
def c7r746targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
def c7r746choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,2),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r746_checked : successorFastRowCheck c7r746targets c7r746 c7r746choice = true := by decide
theorem c7r746_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r746 := by
  refine ⟨c7r746targets, c7r746choice, ?_, c7r746_checked⟩
  intro S h
  simp only [c7r746targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 29 _ (by rfl)))
def c7r747 : List GridPoint := [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)]
def c7r747targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
def c7r747choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,2),(3,(0,0))),((1,4),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r747_checked : successorFastRowCheck c7r747targets c7r747 c7r747choice = true := by decide
theorem c7r747_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r747 := by
  refine ⟨c7r747targets, c7r747choice, ?_, c7r747_checked⟩
  intro S h
  simp only [c7r747targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 5 _ (by rfl)))
def c7r748 : List GridPoint := [(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r748targets : Array (List GridPoint) := #[[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,5),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r748choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((-1,5),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r748_checked : successorFastRowCheck c7r748targets c7r748 c7r748choice = true := by decide
theorem c7r748_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r748 := by
  refine ⟨c7r748targets, c7r748choice, ?_, c7r748_checked⟩
  intro S h
  simp only [c7r748targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 15 _ (by rfl)))
def c7r749 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def c7r749targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
def c7r749choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,6),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r749_checked : successorFastRowCheck c7r749targets c7r749 c7r749choice = true := by decide
theorem c7r749_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r749 := by
  refine ⟨c7r749targets, c7r749choice, ?_, c7r749_checked⟩
  intro S h
  simp only [c7r749targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 26 _ (by rfl)))
def c7r750 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def c7r750targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
def c7r750choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r750_checked : successorFastRowCheck c7r750targets c7r750 c7r750choice = true := by decide
theorem c7r750_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r750 := by
  refine ⟨c7r750targets, c7r750choice, ?_, c7r750_checked⟩
  intro S h
  simp only [c7r750targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 31 _ (by rfl)))
def c7r751 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def c7r751targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
def c7r751choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r751_checked : successorFastRowCheck c7r751targets c7r751 c7r751choice = true := by decide
theorem c7r751_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r751 := by
  refine ⟨c7r751targets, c7r751choice, ?_, c7r751_checked⟩
  intro S h
  simp only [c7r751targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 3 _ (by rfl)))
def c7r752 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def c7r752targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
def c7r752choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r752_checked : successorFastRowCheck c7r752targets c7r752 c7r752choice = true := by decide
theorem c7r752_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r752 := by
  refine ⟨c7r752targets, c7r752choice, ?_, c7r752_checked⟩
  intro S h
  simp only [c7r752targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 6 _ (by rfl)))
def c7r753 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def c7r753targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
def c7r753choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r753_checked : successorFastRowCheck c7r753targets c7r753 c7r753choice = true := by decide
theorem c7r753_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r753 := by
  refine ⟨c7r753targets, c7r753choice, ?_, c7r753_checked⟩
  intro S h
  simp only [c7r753targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 8 _ (by rfl)))
def c7r754 : List GridPoint := [(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def c7r754targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
def c7r754choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r754_checked : successorFastRowCheck c7r754targets c7r754 c7r754choice = true := by decide
theorem c7r754_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r754 := by
  refine ⟨c7r754targets, c7r754choice, ?_, c7r754_checked⟩
  intro S h
  simp only [c7r754targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 10 _ (by rfl)))
def c7r755 : List GridPoint := [(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)]
def c7r755targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
def c7r755choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,1),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r755_checked : successorFastRowCheck c7r755targets c7r755 c7r755choice = true := by decide
theorem c7r755_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r755 := by
  refine ⟨c7r755targets, c7r755choice, ?_, c7r755_checked⟩
  intro S h
  simp only [c7r755targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 22 _ (by rfl)))
def c7r756 : List GridPoint := [(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)]
def c7r756targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
def c7r756choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,2),(1,(0,0))),((0,3),(2,(0,0))),((0,5),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r756_checked : successorFastRowCheck c7r756targets c7r756 c7r756choice = true := by decide
theorem c7r756_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r756 := by
  refine ⟨c7r756targets, c7r756choice, ?_, c7r756_checked⟩
  intro S h
  simp only [c7r756targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 31 _ (by rfl)))
def c7r757 : List GridPoint := [(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)]
def c7r757targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,5),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r757choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,3),(1,(0,0))),((0,5),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r757_checked : successorFastRowCheck c7r757targets c7r757 c7r757choice = true := by decide
theorem c7r757_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r757 := by
  refine ⟨c7r757targets, c7r757choice, ?_, c7r757_checked⟩
  intro S h
  simp only [c7r757targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 8 _ (by rfl)))
def c7r758 : List GridPoint := [(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)]
def c7r758targets : Array (List GridPoint) := #[[(0,4),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
def c7r758choice (b : GridPoint) : ℕ × GridPoint := (([((-1,4),(0,(1,0))),((0,3),(1,(0,0))),((0,5),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r758_checked : successorFastRowCheck c7r758targets c7r758 c7r758choice = true := by decide
theorem c7r758_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r758 := by
  refine ⟨c7r758targets, c7r758choice, ?_, c7r758_checked⟩
  intro S h
  simp only [c7r758targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 18 _ (by rfl)))
def c7r759 : List GridPoint := [(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def c7r759targets : Array (List GridPoint) := #[[(0,5),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
def c7r759choice (b : GridPoint) : ℕ × GridPoint := (([((-1,5),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r759_checked : successorFastRowCheck c7r759targets c7r759 c7r759choice = true := by decide
theorem c7r759_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r759 := by
  refine ⟨c7r759targets, c7r759choice, ?_, c7r759_checked⟩
  intro S h
  simp only [c7r759targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 30 _ (by rfl)))
theorem C7R00736_closed (row : List GridPoint) (h : FamilyMember row F7B000L23) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L23, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r736_closed
  · subst row; exact c7r737_closed
  · subst row; exact c7r738_closed
  · subst row; exact c7r739_closed
  · subst row; exact c7r740_closed
  · subst row; exact c7r741_closed
  · subst row; exact c7r742_closed
  · subst row; exact c7r743_closed
  · subst row; exact c7r744_closed
  · subst row; exact c7r745_closed
  · subst row; exact c7r746_closed
  · subst row; exact c7r747_closed
  · subst row; exact c7r748_closed
  · subst row; exact c7r749_closed
  · subst row; exact c7r750_closed
  · subst row; exact c7r751_closed
  · subst row; exact c7r752_closed
  · subst row; exact c7r753_closed
  · subst row; exact c7r754_closed
  · subst row; exact c7r755_closed
  · subst row; exact c7r756_closed
  · subst row; exact c7r757_closed
  · subst row; exact c7r758_closed
  · subst row; exact c7r759_closed
end Polyomino57
