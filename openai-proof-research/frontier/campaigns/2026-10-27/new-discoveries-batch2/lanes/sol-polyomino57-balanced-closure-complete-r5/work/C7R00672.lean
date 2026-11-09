import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r672 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)]
def c7r672targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
def c7r672choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r672_checked : successorFastRowCheck c7r672targets c7r672 c7r672choice = true := by decide
theorem c7r672_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r672 := by
  refine ⟨c7r672targets, c7r672choice, ?_, c7r672_checked⟩
  intro S h
  simp only [c7r672targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 29 _ (by rfl)))
def c7r673 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)]
def c7r673targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
def c7r673choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r673_checked : successorFastRowCheck c7r673targets c7r673 c7r673choice = true := by decide
theorem c7r673_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r673 := by
  refine ⟨c7r673targets, c7r673choice, ?_, c7r673_checked⟩
  intro S h
  simp only [c7r673targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 0 _ (by rfl)))
def c7r674 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)]
def c7r674targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
def c7r674choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r674_checked : successorFastRowCheck c7r674targets c7r674 c7r674choice = true := by decide
theorem c7r674_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r674 := by
  refine ⟨c7r674targets, c7r674choice, ?_, c7r674_checked⟩
  intro S h
  simp only [c7r674targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 2 _ (by rfl)))
def c7r675 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]
def c7r675targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
def c7r675choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r675_checked : successorFastRowCheck c7r675targets c7r675 c7r675choice = true := by decide
theorem c7r675_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r675 := by
  refine ⟨c7r675targets, c7r675choice, ?_, c7r675_checked⟩
  intro S h
  simp only [c7r675targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 4 _ (by rfl)))
def c7r676 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)]
def c7r676targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r676choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r676_checked : successorFastRowCheck c7r676targets c7r676 c7r676choice = true := by decide
theorem c7r676_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r676 := by
  refine ⟨c7r676targets, c7r676choice, ?_, c7r676_checked⟩
  intro S h
  simp only [c7r676targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 7 _ (by rfl)))
def c7r677 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)]
def c7r677targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
def c7r677choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r677_checked : successorFastRowCheck c7r677targets c7r677 c7r677choice = true := by decide
theorem c7r677_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r677 := by
  refine ⟨c7r677targets, c7r677choice, ?_, c7r677_checked⟩
  intro S h
  simp only [c7r677targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 10 _ (by rfl)))
def c7r678 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]
def c7r678targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
def c7r678choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r678_checked : successorFastRowCheck c7r678targets c7r678 c7r678choice = true := by decide
theorem c7r678_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r678 := by
  refine ⟨c7r678targets, c7r678choice, ?_, c7r678_checked⟩
  intro S h
  simp only [c7r678targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 12 _ (by rfl)))
def c7r679 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)]
def c7r679targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
def c7r679choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r679_checked : successorFastRowCheck c7r679targets c7r679 c7r679choice = true := by decide
theorem c7r679_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r679 := by
  refine ⟨c7r679targets, c7r679choice, ?_, c7r679_checked⟩
  intro S h
  simp only [c7r679targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 15 _ (by rfl)))
def c7r680 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]
def c7r680targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
def c7r680choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r680_checked : successorFastRowCheck c7r680targets c7r680 c7r680choice = true := by decide
theorem c7r680_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r680 := by
  refine ⟨c7r680targets, c7r680choice, ?_, c7r680_checked⟩
  intro S h
  simp only [c7r680targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 18 _ (by rfl)))
def c7r681 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)]
def c7r681targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
def c7r681choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r681_checked : successorFastRowCheck c7r681targets c7r681 c7r681choice = true := by decide
theorem c7r681_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r681 := by
  refine ⟨c7r681targets, c7r681choice, ?_, c7r681_checked⟩
  intro S h
  simp only [c7r681targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 21 _ (by rfl)))
def c7r682 : List GridPoint := [(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]
def c7r682targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
def c7r682choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r682_checked : successorFastRowCheck c7r682targets c7r682 c7r682choice = true := by decide
theorem c7r682_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r682 := by
  refine ⟨c7r682targets, c7r682choice, ?_, c7r682_checked⟩
  intro S h
  simp only [c7r682targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 24 _ (by rfl)))
def c7r683 : List GridPoint := [(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)]
def c7r683targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
def c7r683choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,0),(3,(0,0))),((1,1),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r683_checked : successorFastRowCheck c7r683targets c7r683 c7r683choice = true := by decide
theorem c7r683_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r683 := by
  refine ⟨c7r683targets, c7r683choice, ?_, c7r683_checked⟩
  intro S h
  simp only [c7r683targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 29 _ (by rfl)))
def c7r684 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)]
def c7r684targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
def c7r684choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,4),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r684_checked : successorFastRowCheck c7r684targets c7r684 c7r684choice = true := by decide
theorem c7r684_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r684 := by
  refine ⟨c7r684targets, c7r684choice, ?_, c7r684_checked⟩
  intro S h
  simp only [c7r684targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 2 _ (by rfl)))
def c7r685 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)]
def c7r685targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
def c7r685choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r685_checked : successorFastRowCheck c7r685targets c7r685 c7r685choice = true := by decide
theorem c7r685_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r685 := by
  refine ⟨c7r685targets, c7r685choice, ?_, c7r685_checked⟩
  intro S h
  simp only [c7r685targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 7 _ (by rfl)))
def c7r686 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)]
def c7r686targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
def c7r686choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r686_checked : successorFastRowCheck c7r686targets c7r686 c7r686choice = true := by decide
theorem c7r686_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r686 := by
  refine ⟨c7r686targets, c7r686choice, ?_, c7r686_checked⟩
  intro S h
  simp only [c7r686targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 9 _ (by rfl)))
def c7r687 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)]
def c7r687targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
def c7r687choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r687_checked : successorFastRowCheck c7r687targets c7r687 c7r687choice = true := by decide
theorem c7r687_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r687 := by
  refine ⟨c7r687targets, c7r687choice, ?_, c7r687_checked⟩
  intro S h
  simp only [c7r687targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 11 _ (by rfl)))
def c7r688 : List GridPoint := [(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)]
def c7r688targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
def c7r688choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r688_checked : successorFastRowCheck c7r688targets c7r688 c7r688choice = true := by decide
theorem c7r688_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r688 := by
  refine ⟨c7r688targets, c7r688choice, ?_, c7r688_checked⟩
  intro S h
  simp only [c7r688targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L17_lift _ (familyLookup_sound F8B001L17 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 15 _ (by rfl)))
def c7r689 : List GridPoint := [(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)]
def c7r689targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
def c7r689choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r689_checked : successorFastRowCheck c7r689targets c7r689 c7r689choice = true := by decide
theorem c7r689_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r689 := by
  refine ⟨c7r689targets, c7r689choice, ?_, c7r689_checked⟩
  intro S h
  simp only [c7r689targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 22 _ (by rfl)))
def c7r690 : List GridPoint := [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)]
def c7r690targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
def c7r690choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r690_checked : successorFastRowCheck c7r690targets c7r690 c7r690choice = true := by decide
theorem c7r690_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r690 := by
  refine ⟨c7r690targets, c7r690choice, ?_, c7r690_checked⟩
  intro S h
  simp only [c7r690targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 29 _ (by rfl)))
def c7r691 : List GridPoint := [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)]
def c7r691targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
def c7r691choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r691_checked : successorFastRowCheck c7r691targets c7r691 c7r691choice = true := by decide
theorem c7r691_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r691 := by
  refine ⟨c7r691targets, c7r691choice, ?_, c7r691_checked⟩
  intro S h
  simp only [c7r691targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 0 _ (by rfl)))
def c7r692 : List GridPoint := [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)]
def c7r692targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
def c7r692choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r692_checked : successorFastRowCheck c7r692targets c7r692 c7r692choice = true := by decide
theorem c7r692_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r692 := by
  refine ⟨c7r692targets, c7r692choice, ?_, c7r692_checked⟩
  intro S h
  simp only [c7r692targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 2 _ (by rfl)))
def c7r693 : List GridPoint := [(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)]
def c7r693targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
def c7r693choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r693_checked : successorFastRowCheck c7r693targets c7r693 c7r693choice = true := by decide
theorem c7r693_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r693 := by
  refine ⟨c7r693targets, c7r693choice, ?_, c7r693_checked⟩
  intro S h
  simp only [c7r693targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 4 _ (by rfl)))
def c7r694 : List GridPoint := [(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)]
def c7r694targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
def c7r694choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,1),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r694_checked : successorFastRowCheck c7r694targets c7r694 c7r694choice = true := by decide
theorem c7r694_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r694 := by
  refine ⟨c7r694targets, c7r694choice, ?_, c7r694_checked⟩
  intro S h
  simp only [c7r694targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 9 _ (by rfl)))
def c7r695 : List GridPoint := [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)]
def c7r695targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)]]
def c7r695choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,1),(1,(0,0))),((0,3),(2,(0,0))),((1,1),(3,(0,0))),((1,3),(4,(0,0))),((2,1),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r695_checked : successorFastRowCheck c7r695targets c7r695 c7r695choice = true := by decide
theorem c7r695_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r695 := by
  refine ⟨c7r695targets, c7r695choice, ?_, c7r695_checked⟩
  intro S h
  simp only [c7r695targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 15 _ (by rfl)))
def c7r696 : List GridPoint := [(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)]
def c7r696targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3)],[(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)]]
def c7r696choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((-1,4),(1,(1,0))),((-1,5),(2,(1,0))),((0,0),(3,(0,0))),((0,1),(4,(0,0))),((0,2),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,4),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r696_checked : successorFastRowCheck c7r696targets c7r696 c7r696choice = true := by decide
theorem c7r696_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r696 := by
  refine ⟨c7r696targets, c7r696choice, ?_, c7r696_checked⟩
  intro S h
  simp only [c7r696targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 24 _ (by rfl)))
def c7r697 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r697targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r697choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r697_checked : successorFastRowCheck c7r697targets c7r697 c7r697choice = true := by decide
theorem c7r697_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r697 := by
  refine ⟨c7r697targets, c7r697choice, ?_, c7r697_checked⟩
  intro S h
  simp only [c7r697targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 1 _ (by rfl)))
def c7r698 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)]
def c7r698targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
def c7r698choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r698_checked : successorFastRowCheck c7r698targets c7r698 c7r698choice = true := by decide
theorem c7r698_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r698 := by
  refine ⟨c7r698targets, c7r698choice, ?_, c7r698_checked⟩
  intro S h
  simp only [c7r698targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 5 _ (by rfl)))
def c7r699 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)]
def c7r699targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
def c7r699choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r699_checked : successorFastRowCheck c7r699targets c7r699 c7r699choice = true := by decide
theorem c7r699_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r699 := by
  refine ⟨c7r699targets, c7r699choice, ?_, c7r699_checked⟩
  intro S h
  simp only [c7r699targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 8 _ (by rfl)))
def c7r700 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)]
def c7r700targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
def c7r700choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r700_checked : successorFastRowCheck c7r700targets c7r700 c7r700choice = true := by decide
theorem c7r700_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r700 := by
  refine ⟨c7r700targets, c7r700choice, ?_, c7r700_checked⟩
  intro S h
  simp only [c7r700targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 10 _ (by rfl)))
def c7r701 : List GridPoint := [(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)]
def c7r701targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
def c7r701choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((-1,4),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r701_checked : successorFastRowCheck c7r701targets c7r701 c7r701choice = true := by decide
theorem c7r701_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r701 := by
  refine ⟨c7r701targets, c7r701choice, ?_, c7r701_checked⟩
  intro S h
  simp only [c7r701targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 12 _ (by rfl)))
def c7r702 : List GridPoint := [(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)]
def c7r702targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
def c7r702choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((-1,4),(1,(1,0))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r702_checked : successorFastRowCheck c7r702targets c7r702 c7r702choice = true := by decide
theorem c7r702_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r702 := by
  refine ⟨c7r702targets, c7r702choice, ?_, c7r702_checked⟩
  intro S h
  simp only [c7r702targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 20 _ (by rfl)))
def c7r703 : List GridPoint := [(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)]
def c7r703targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(0,5),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
def c7r703choice (b : GridPoint) : ℕ × GridPoint := (([((-1,3),(0,(1,0))),((-1,4),(1,(1,0))),((0,2),(2,(0,0))),((0,5),(3,(0,0))),((1,0),(4,(0,0))),((1,1),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r703_checked : successorFastRowCheck c7r703targets c7r703 c7r703choice = true := by decide
theorem c7r703_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r703 := by
  refine ⟨c7r703targets, c7r703choice, ?_, c7r703_checked⟩
  intro S h
  simp only [c7r703targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L16_lift _ (familyLookup_sound F8B001L16 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L11_lift _ (familyLookup_sound F8B001L11 [] 27 _ (by rfl)))
theorem C7R00672_closed (row : List GridPoint) (h : FamilyMember row F7B000L21) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L21, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r672_closed
  · subst row; exact c7r673_closed
  · subst row; exact c7r674_closed
  · subst row; exact c7r675_closed
  · subst row; exact c7r676_closed
  · subst row; exact c7r677_closed
  · subst row; exact c7r678_closed
  · subst row; exact c7r679_closed
  · subst row; exact c7r680_closed
  · subst row; exact c7r681_closed
  · subst row; exact c7r682_closed
  · subst row; exact c7r683_closed
  · subst row; exact c7r684_closed
  · subst row; exact c7r685_closed
  · subst row; exact c7r686_closed
  · subst row; exact c7r687_closed
  · subst row; exact c7r688_closed
  · subst row; exact c7r689_closed
  · subst row; exact c7r690_closed
  · subst row; exact c7r691_closed
  · subst row; exact c7r692_closed
  · subst row; exact c7r693_closed
  · subst row; exact c7r694_closed
  · subst row; exact c7r695_closed
  · subst row; exact c7r696_closed
  · subst row; exact c7r697_closed
  · subst row; exact c7r698_closed
  · subst row; exact c7r699_closed
  · subst row; exact c7r700_closed
  · subst row; exact c7r701_closed
  · subst row; exact c7r702_closed
  · subst row; exact c7r703_closed
end Polyomino57
