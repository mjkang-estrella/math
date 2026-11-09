import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r704 : List GridPoint := [(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)]
def c7r704targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(0,5),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r704choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((-1,4),(1,(1,0))),((0,2),(2,(0,0))),((0,5),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r704_checked : successorFastRowCheck c7r704targets c7r704 c7r704choice = true := by decide
theorem c7r704_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r704 := by
  refine ⟨c7r704targets, c7r704choice, ?_, c7r704_checked⟩
  intro S h
  simp only [c7r704targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 3 _ (by rfl)))
def c7r705 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def c7r705targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
def c7r705choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,6),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r705_checked : successorFastRowCheck c7r705targets c7r705 c7r705choice = true := by decide
theorem c7r705_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r705 := by
  refine ⟨c7r705targets, c7r705choice, ?_, c7r705_checked⟩
  intro S h
  simp only [c7r705targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 15 _ (by rfl)))
def c7r706 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def c7r706targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
def c7r706choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r706_checked : successorFastRowCheck c7r706targets c7r706 c7r706choice = true := by decide
theorem c7r706_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r706 := by
  refine ⟨c7r706targets, c7r706choice, ?_, c7r706_checked⟩
  intro S h
  simp only [c7r706targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 20 _ (by rfl)))
def c7r707 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def c7r707targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
def c7r707choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r707_checked : successorFastRowCheck c7r707targets c7r707 c7r707choice = true := by decide
theorem c7r707_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r707 := by
  refine ⟨c7r707targets, c7r707choice, ?_, c7r707_checked⟩
  intro S h
  simp only [c7r707targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 24 _ (by rfl)))
def c7r708 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def c7r708targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
def c7r708choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r708_checked : successorFastRowCheck c7r708targets c7r708 c7r708choice = true := by decide
theorem c7r708_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r708 := by
  refine ⟨c7r708targets, c7r708choice, ?_, c7r708_checked⟩
  intro S h
  simp only [c7r708targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 27 _ (by rfl)))
def c7r709 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def c7r709targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
def c7r709choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r709_checked : successorFastRowCheck c7r709targets c7r709 c7r709choice = true := by decide
theorem c7r709_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r709 := by
  refine ⟨c7r709targets, c7r709choice, ?_, c7r709_checked⟩
  intro S h
  simp only [c7r709targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 29 _ (by rfl)))
def c7r710 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def c7r710targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
def c7r710choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r710_checked : successorFastRowCheck c7r710targets c7r710 c7r710choice = true := by decide
theorem c7r710_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r710 := by
  refine ⟨c7r710targets, c7r710choice, ?_, c7r710_checked⟩
  intro S h
  simp only [c7r710targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 31 _ (by rfl)))
def c7r711 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]
def c7r711targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
def c7r711choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r711_checked : successorFastRowCheck c7r711targets c7r711 c7r711choice = true := by decide
theorem c7r711_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r711 := by
  refine ⟨c7r711targets, c7r711choice, ?_, c7r711_checked⟩
  intro S h
  simp only [c7r711targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 3 _ (by rfl)))
def c7r712 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)]
def c7r712targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
def c7r712choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r712_checked : successorFastRowCheck c7r712targets c7r712 c7r712choice = true := by decide
theorem c7r712_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r712 := by
  refine ⟨c7r712targets, c7r712choice, ?_, c7r712_checked⟩
  intro S h
  simp only [c7r712targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 6 _ (by rfl)))
def c7r713 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)]
def c7r713targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
def c7r713choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r713_checked : successorFastRowCheck c7r713targets c7r713 c7r713choice = true := by decide
theorem c7r713_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r713 := by
  refine ⟨c7r713targets, c7r713choice, ?_, c7r713_checked⟩
  intro S h
  simp only [c7r713targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 9 _ (by rfl)))
def c7r714 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]
def c7r714targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
def c7r714choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r714_checked : successorFastRowCheck c7r714targets c7r714 c7r714choice = true := by decide
theorem c7r714_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r714 := by
  refine ⟨c7r714targets, c7r714choice, ?_, c7r714_checked⟩
  intro S h
  simp only [c7r714targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 11 _ (by rfl)))
def c7r715 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]
def c7r715targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
def c7r715choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r715_checked : successorFastRowCheck c7r715targets c7r715 c7r715choice = true := by decide
theorem c7r715_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r715 := by
  refine ⟨c7r715targets, c7r715choice, ?_, c7r715_checked⟩
  intro S h
  simp only [c7r715targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 14 _ (by rfl)))
def c7r716 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)]
def c7r716targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
def c7r716choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r716_checked : successorFastRowCheck c7r716targets c7r716 c7r716choice = true := by decide
theorem c7r716_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r716 := by
  refine ⟨c7r716targets, c7r716choice, ?_, c7r716_checked⟩
  intro S h
  simp only [c7r716targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 17 _ (by rfl)))
def c7r717 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]
def c7r717targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
def c7r717choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r717_checked : successorFastRowCheck c7r717targets c7r717 c7r717choice = true := by decide
theorem c7r717_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r717 := by
  refine ⟨c7r717targets, c7r717choice, ?_, c7r717_checked⟩
  intro S h
  simp only [c7r717targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 20 _ (by rfl)))
def c7r718 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)]
def c7r718targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
def c7r718choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r718_checked : successorFastRowCheck c7r718targets c7r718 c7r718choice = true := by decide
theorem c7r718_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r718 := by
  refine ⟨c7r718targets, c7r718choice, ?_, c7r718_checked⟩
  intro S h
  simp only [c7r718targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 23 _ (by rfl)))
def c7r719 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]
def c7r719targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
def c7r719choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r719_checked : successorFastRowCheck c7r719targets c7r719 c7r719choice = true := by decide
theorem c7r719_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r719 := by
  refine ⟨c7r719targets, c7r719choice, ?_, c7r719_checked⟩
  intro S h
  simp only [c7r719targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 26 _ (by rfl)))
def c7r720 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)]
def c7r720targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
def c7r720choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r720_checked : successorFastRowCheck c7r720targets c7r720 c7r720choice = true := by decide
theorem c7r720_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r720 := by
  refine ⟨c7r720targets, c7r720choice, ?_, c7r720_checked⟩
  intro S h
  simp only [c7r720targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 29 _ (by rfl)))
def c7r721 : List GridPoint := [(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]
def c7r721targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
def c7r721choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r721_checked : successorFastRowCheck c7r721targets c7r721 c7r721choice = true := by decide
theorem c7r721_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r721 := by
  refine ⟨c7r721targets, c7r721choice, ?_, c7r721_checked⟩
  intro S h
  simp only [c7r721targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 0 _ (by rfl)))
def c7r722 : List GridPoint := [(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)]
def c7r722targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
def c7r722choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r722_checked : successorFastRowCheck c7r722targets c7r722 c7r722choice = true := by decide
theorem c7r722_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r722 := by
  refine ⟨c7r722targets, c7r722choice, ?_, c7r722_checked⟩
  intro S h
  simp only [c7r722targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 6 _ (by rfl)))
def c7r723 : List GridPoint := [(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)]
def c7r723targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
def c7r723choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r723_checked : successorFastRowCheck c7r723targets c7r723 c7r723choice = true := by decide
theorem c7r723_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r723 := by
  refine ⟨c7r723targets, c7r723choice, ?_, c7r723_checked⟩
  intro S h
  simp only [c7r723targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 11 _ (by rfl)))
def c7r724 : List GridPoint := [(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)]
def c7r724targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r724choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r724_checked : successorFastRowCheck c7r724targets c7r724 c7r724choice = true := by decide
theorem c7r724_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r724 := by
  refine ⟨c7r724targets, c7r724choice, ?_, c7r724_checked⟩
  intro S h
  simp only [c7r724targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 17 _ (by rfl)))
def c7r725 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)]
def c7r725targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
def c7r725choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,1),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,5),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r725_checked : successorFastRowCheck c7r725targets c7r725 c7r725choice = true := by decide
theorem c7r725_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r725 := by
  refine ⟨c7r725targets, c7r725choice, ?_, c7r725_checked⟩
  intro S h
  simp only [c7r725targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 23 _ (by rfl)))
def c7r726 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)]
def c7r726targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
def c7r726choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,1),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r726_checked : successorFastRowCheck c7r726targets c7r726 c7r726choice = true := by decide
theorem c7r726_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r726 := by
  refine ⟨c7r726targets, c7r726choice, ?_, c7r726_checked⟩
  intro S h
  simp only [c7r726targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 28 _ (by rfl)))
def c7r727 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)]
def c7r727targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]
def c7r727choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,1),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r727_checked : successorFastRowCheck c7r727targets c7r727 c7r727choice = true := by decide
theorem c7r727_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r727 := by
  refine ⟨c7r727targets, c7r727choice, ?_, c7r727_checked⟩
  intro S h
  simp only [c7r727targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 0 _ (by rfl)))
def c7r728 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)]
def c7r728targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)]]
def c7r728choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,1),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r728_checked : successorFastRowCheck c7r728targets c7r728 c7r728choice = true := by decide
theorem c7r728_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r728 := by
  refine ⟨c7r728targets, c7r728choice, ?_, c7r728_checked⟩
  intro S h
  simp only [c7r728targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 2 _ (by rfl)))
def c7r729 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]
def c7r729targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)]]
def c7r729choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,1),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r729_checked : successorFastRowCheck c7r729targets c7r729 c7r729choice = true := by decide
theorem c7r729_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r729 := by
  refine ⟨c7r729targets, c7r729choice, ?_, c7r729_checked⟩
  intro S h
  simp only [c7r729targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 4 _ (by rfl)))
def c7r730 : List GridPoint := [(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)]
def c7r730targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)]]
def c7r730choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,1),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r730_checked : successorFastRowCheck c7r730targets c7r730 c7r730choice = true := by decide
theorem c7r730_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r730 := by
  refine ⟨c7r730targets, c7r730choice, ?_, c7r730_checked⟩
  intro S h
  simp only [c7r730targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 9 _ (by rfl)))
def c7r731 : List GridPoint := [(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)]
def c7r731targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r731choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,1),(1,(0,0))),((0,2),(2,(0,0))),((0,4),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r731_checked : successorFastRowCheck c7r731targets c7r731 c7r731choice = true := by decide
theorem c7r731_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r731 := by
  refine ⟨c7r731targets, c7r731choice, ?_, c7r731_checked⟩
  intro S h
  simp only [c7r731targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 17 _ (by rfl)))
def c7r732 : List GridPoint := [(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)]
def c7r732targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
def c7r732choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,5),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r732_checked : successorFastRowCheck c7r732targets c7r732 c7r732choice = true := by decide
theorem c7r732_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r732 := by
  refine ⟨c7r732targets, c7r732choice, ?_, c7r732_checked⟩
  intro S h
  simp only [c7r732targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 24 _ (by rfl)))
def c7r733 : List GridPoint := [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)]
def c7r733targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r733choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r733_checked : successorFastRowCheck c7r733targets c7r733 c7r733choice = true := by decide
theorem c7r733_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r733 := by
  refine ⟨c7r733targets, c7r733choice, ?_, c7r733_checked⟩
  intro S h
  simp only [c7r733targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 31 _ (by rfl)))
def c7r734 : List GridPoint := [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)]
def c7r734targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r734choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r734_checked : successorFastRowCheck c7r734targets c7r734 c7r734choice = true := by decide
theorem c7r734_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r734 := by
  refine ⟨c7r734targets, c7r734choice, ?_, c7r734_checked⟩
  intro S h
  simp only [c7r734targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 2 _ (by rfl)))
def c7r735 : List GridPoint := [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)]
def c7r735targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r735choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((0,2),(1,(0,0))),((0,4),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r735_checked : successorFastRowCheck c7r735targets c7r735 c7r735choice = true := by decide
theorem c7r735_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r735 := by
  refine ⟨c7r735targets, c7r735choice, ?_, c7r735_checked⟩
  intro S h
  simp only [c7r735targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 4 _ (by rfl)))
theorem C7R00704_closed (row : List GridPoint) (h : FamilyMember row F7B000L22) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L22, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r704_closed
  · subst row; exact c7r705_closed
  · subst row; exact c7r706_closed
  · subst row; exact c7r707_closed
  · subst row; exact c7r708_closed
  · subst row; exact c7r709_closed
  · subst row; exact c7r710_closed
  · subst row; exact c7r711_closed
  · subst row; exact c7r712_closed
  · subst row; exact c7r713_closed
  · subst row; exact c7r714_closed
  · subst row; exact c7r715_closed
  · subst row; exact c7r716_closed
  · subst row; exact c7r717_closed
  · subst row; exact c7r718_closed
  · subst row; exact c7r719_closed
  · subst row; exact c7r720_closed
  · subst row; exact c7r721_closed
  · subst row; exact c7r722_closed
  · subst row; exact c7r723_closed
  · subst row; exact c7r724_closed
  · subst row; exact c7r725_closed
  · subst row; exact c7r726_closed
  · subst row; exact c7r727_closed
  · subst row; exact c7r728_closed
  · subst row; exact c7r729_closed
  · subst row; exact c7r730_closed
  · subst row; exact c7r731_closed
  · subst row; exact c7r732_closed
  · subst row; exact c7r733_closed
  · subst row; exact c7r734_closed
  · subst row; exact c7r735_closed
end Polyomino57
