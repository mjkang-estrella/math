import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r544 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)]
def c7r544targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
def c7r544choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r544_checked : successorFastRowCheck c7r544targets c7r544 c7r544choice = true := by decide
theorem c7r544_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r544 := by
  refine ⟨c7r544targets, c7r544choice, ?_, c7r544_checked⟩
  intro S h
  simp only [c7r544targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 23 _ (by rfl)))
def c7r545 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]
def c7r545targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
def c7r545choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r545_checked : successorFastRowCheck c7r545targets c7r545 c7r545choice = true := by decide
theorem c7r545_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r545 := by
  refine ⟨c7r545targets, c7r545choice, ?_, c7r545_checked⟩
  intro S h
  simp only [c7r545targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 25 _ (by rfl)))
def c7r546 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)]
def c7r546targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
def c7r546choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r546_checked : successorFastRowCheck c7r546targets c7r546 c7r546choice = true := by decide
theorem c7r546_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r546 := by
  refine ⟨c7r546targets, c7r546choice, ?_, c7r546_checked⟩
  intro S h
  simp only [c7r546targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 28 _ (by rfl)))
def c7r547 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)]
def c7r547targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
def c7r547choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r547_checked : successorFastRowCheck c7r547targets c7r547 c7r547choice = true := by decide
theorem c7r547_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r547 := by
  refine ⟨c7r547targets, c7r547choice, ?_, c7r547_checked⟩
  intro S h
  simp only [c7r547targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 31 _ (by rfl)))
def c7r548 : List GridPoint := [(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]
def c7r548targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
def c7r548choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r548_checked : successorFastRowCheck c7r548targets c7r548 c7r548choice = true := by decide
theorem c7r548_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r548 := by
  refine ⟨c7r548targets, c7r548choice, ?_, c7r548_checked⟩
  intro S h
  simp only [c7r548targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 2 _ (by rfl)))
def c7r549 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)]
def c7r549targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
def c7r549choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r549_checked : successorFastRowCheck c7r549targets c7r549 c7r549choice = true := by decide
theorem c7r549_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r549 := by
  refine ⟨c7r549targets, c7r549choice, ?_, c7r549_checked⟩
  intro S h
  simp only [c7r549targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 7 _ (by rfl)))
def c7r550 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)]
def c7r550targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
def c7r550choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r550_checked : successorFastRowCheck c7r550targets c7r550 c7r550choice = true := by decide
theorem c7r550_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r550 := by
  refine ⟨c7r550targets, c7r550choice, ?_, c7r550_checked⟩
  intro S h
  simp only [c7r550targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 12 _ (by rfl)))
def c7r551 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)]
def c7r551targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
def c7r551choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r551_checked : successorFastRowCheck c7r551targets c7r551 c7r551choice = true := by decide
theorem c7r551_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r551 := by
  refine ⟨c7r551targets, c7r551choice, ?_, c7r551_checked⟩
  intro S h
  simp only [c7r551targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 14 _ (by rfl)))
def c7r552 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]
def c7r552targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
def c7r552choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r552_checked : successorFastRowCheck c7r552targets c7r552 c7r552choice = true := by decide
theorem c7r552_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r552 := by
  refine ⟨c7r552targets, c7r552choice, ?_, c7r552_checked⟩
  intro S h
  simp only [c7r552targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 16 _ (by rfl)))
def c7r553 : List GridPoint := [(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)]
def c7r553targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
def c7r553choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r553_checked : successorFastRowCheck c7r553targets c7r553 c7r553choice = true := by decide
theorem c7r553_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r553 := by
  refine ⟨c7r553targets, c7r553choice, ?_, c7r553_checked⟩
  intro S h
  simp only [c7r553targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 20 _ (by rfl)))
def c7r554 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)]
def c7r554targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
def c7r554choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r554_checked : successorFastRowCheck c7r554targets c7r554 c7r554choice = true := by decide
theorem c7r554_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r554 := by
  refine ⟨c7r554targets, c7r554choice, ?_, c7r554_checked⟩
  intro S h
  simp only [c7r554targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 28 _ (by rfl)))
def c7r555 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)]
def c7r555targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
def c7r555choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r555_checked : successorFastRowCheck c7r555targets c7r555 c7r555choice = true := by decide
theorem c7r555_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r555 := by
  refine ⟨c7r555targets, c7r555choice, ?_, c7r555_checked⟩
  intro S h
  simp only [c7r555targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 31 _ (by rfl)))
def c7r556 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)]
def c7r556targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
def c7r556choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r556_checked : successorFastRowCheck c7r556targets c7r556 c7r556choice = true := by decide
theorem c7r556_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r556 := by
  refine ⟨c7r556targets, c7r556choice, ?_, c7r556_checked⟩
  intro S h
  simp only [c7r556targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 1 _ (by rfl)))
def c7r557 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]
def c7r557targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
def c7r557choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r557_checked : successorFastRowCheck c7r557targets c7r557 c7r557choice = true := by decide
theorem c7r557_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r557 := by
  refine ⟨c7r557targets, c7r557choice, ?_, c7r557_checked⟩
  intro S h
  simp only [c7r557targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L9_lift _ (familyLookup_sound F8B001L9 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 3 _ (by rfl)))
def c7r558 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)]
def c7r558targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
def c7r558choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r558_checked : successorFastRowCheck c7r558targets c7r558 c7r558choice = true := by decide
theorem c7r558_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r558 := by
  refine ⟨c7r558targets, c7r558choice, ?_, c7r558_checked⟩
  intro S h
  simp only [c7r558targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 6 _ (by rfl)))
def c7r559 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]
def c7r559targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
def c7r559choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r559_checked : successorFastRowCheck c7r559targets c7r559 c7r559choice = true := by decide
theorem c7r559_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r559 := by
  refine ⟨c7r559targets, c7r559choice, ?_, c7r559_checked⟩
  intro S h
  simp only [c7r559targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 8 _ (by rfl)))
def c7r560 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)]
def c7r560targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
def c7r560choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r560_checked : successorFastRowCheck c7r560targets c7r560 c7r560choice = true := by decide
theorem c7r560_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r560 := by
  refine ⟨c7r560targets, c7r560choice, ?_, c7r560_checked⟩
  intro S h
  simp only [c7r560targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 11 _ (by rfl)))
def c7r561 : List GridPoint := [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]
def c7r561targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
def c7r561choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r561_checked : successorFastRowCheck c7r561targets c7r561 c7r561choice = true := by decide
theorem c7r561_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r561 := by
  refine ⟨c7r561targets, c7r561choice, ?_, c7r561_checked⟩
  intro S h
  simp only [c7r561targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 14 _ (by rfl)))
def c7r562 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)]
def c7r562targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
def c7r562choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r562_checked : successorFastRowCheck c7r562targets c7r562 c7r562choice = true := by decide
theorem c7r562_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r562 := by
  refine ⟨c7r562targets, c7r562choice, ?_, c7r562_checked⟩
  intro S h
  simp only [c7r562targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 18 _ (by rfl)))
def c7r563 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)]
def c7r563targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
def c7r563choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,3),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r563_checked : successorFastRowCheck c7r563targets c7r563 c7r563choice = true := by decide
theorem c7r563_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r563 := by
  refine ⟨c7r563targets, c7r563choice, ?_, c7r563_checked⟩
  intro S h
  simp only [c7r563targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 23 _ (by rfl)))
def c7r564 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)]
def c7r564targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
def c7r564choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r564_checked : successorFastRowCheck c7r564targets c7r564 c7r564choice = true := by decide
theorem c7r564_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r564 := by
  refine ⟨c7r564targets, c7r564choice, ?_, c7r564_checked⟩
  intro S h
  simp only [c7r564targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 25 _ (by rfl)))
def c7r565 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]
def c7r565targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
def c7r565choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r565_checked : successorFastRowCheck c7r565targets c7r565 c7r565choice = true := by decide
theorem c7r565_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r565 := by
  refine ⟨c7r565targets, c7r565choice, ?_, c7r565_checked⟩
  intro S h
  simp only [c7r565targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 27 _ (by rfl)))
def c7r566 : List GridPoint := [(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)]
def c7r566targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
def c7r566choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r566_checked : successorFastRowCheck c7r566targets c7r566 c7r566choice = true := by decide
theorem c7r566_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r566 := by
  refine ⟨c7r566targets, c7r566choice, ?_, c7r566_checked⟩
  intro S h
  simp only [c7r566targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 31 _ (by rfl)))
def c7r567 : List GridPoint := [(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)]
def c7r567targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)]]
def c7r567choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((-1,5),(3,(1,0))),((0,0),(4,(0,0))),((0,1),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((1,5),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0))),((2,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r567_checked : successorFastRowCheck c7r567targets c7r567 c7r567choice = true := by decide
theorem c7r567_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r567 := by
  refine ⟨c7r567targets, c7r567choice, ?_, c7r567_checked⟩
  intro S h
  simp only [c7r567targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 7 _ (by rfl)))
def c7r568 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)]
def c7r568targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)]]
def c7r568choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,1),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r568_checked : successorFastRowCheck c7r568targets c7r568 c7r568choice = true := by decide
theorem c7r568_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r568 := by
  refine ⟨c7r568targets, c7r568choice, ?_, c7r568_checked⟩
  intro S h
  simp only [c7r568targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 14 _ (by rfl)))
def c7r569 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)]
def c7r569targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4)]]
def c7r569choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,1),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r569_checked : successorFastRowCheck c7r569targets c7r569 c7r569choice = true := by decide
theorem c7r569_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r569 := by
  refine ⟨c7r569targets, c7r569choice, ?_, c7r569_checked⟩
  intro S h
  simp only [c7r569targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 19 _ (by rfl)))
def c7r570 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)]
def c7r570targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0)]]
def c7r570choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,1),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r570_checked : successorFastRowCheck c7r570targets c7r570 c7r570choice = true := by decide
theorem c7r570_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r570 := by
  refine ⟨c7r570targets, c7r570choice, ?_, c7r570_checked⟩
  intro S h
  simp only [c7r570targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 22 _ (by rfl)))
def c7r571 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)]
def c7r571targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)]]
def c7r571choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,1),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r571_checked : successorFastRowCheck c7r571targets c7r571 c7r571choice = true := by decide
theorem c7r571_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r571 := by
  refine ⟨c7r571targets, c7r571choice, ?_, c7r571_checked⟩
  intro S h
  simp only [c7r571targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 24 _ (by rfl)))
def c7r572 : List GridPoint := [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)]
def c7r572targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)]]
def c7r572choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,0),(3,(0,0))),((0,1),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r572_checked : successorFastRowCheck c7r572targets c7r572 c7r572choice = true := by decide
theorem c7r572_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r572 := by
  refine ⟨c7r572targets, c7r572choice, ?_, c7r572_checked⟩
  intro S h
  simp only [c7r572targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 26 _ (by rfl)))
def c7r573 : List GridPoint := [(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)]
def c7r573targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)]]
def c7r573choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r573_checked : successorFastRowCheck c7r573targets c7r573 c7r573choice = true := by decide
theorem c7r573_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r573 := by
  refine ⟨c7r573targets, c7r573choice, ?_, c7r573_checked⟩
  intro S h
  simp only [c7r573targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 0 _ (by rfl)))
def c7r574 : List GridPoint := [(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)]
def c7r574targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r574choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,1),(3,(0,0))),((0,5),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,-1),(9,(0,1))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r574_checked : successorFastRowCheck c7r574targets c7r574 c7r574choice = true := by decide
theorem c7r574_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r574 := by
  refine ⟨c7r574targets, c7r574choice, ?_, c7r574_checked⟩
  intro S h
  simp only [c7r574targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 7 _ (by rfl)))
def c7r575 : List GridPoint := [(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r575targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r575choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((-1,3),(1,(1,0))),((0,0),(2,(0,0))),((0,1),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r575_checked : successorFastRowCheck c7r575targets c7r575 c7r575choice = true := by decide
theorem c7r575_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r575 := by
  refine ⟨c7r575targets, c7r575choice, ?_, c7r575_checked⟩
  intro S h
  simp only [c7r575targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L10_lift _ (familyLookup_sound F8B001L10 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 16 _ (by rfl)))
theorem C7R00544_closed (row : List GridPoint) (h : FamilyMember row F7B000L17) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L17, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r544_closed
  · subst row; exact c7r545_closed
  · subst row; exact c7r546_closed
  · subst row; exact c7r547_closed
  · subst row; exact c7r548_closed
  · subst row; exact c7r549_closed
  · subst row; exact c7r550_closed
  · subst row; exact c7r551_closed
  · subst row; exact c7r552_closed
  · subst row; exact c7r553_closed
  · subst row; exact c7r554_closed
  · subst row; exact c7r555_closed
  · subst row; exact c7r556_closed
  · subst row; exact c7r557_closed
  · subst row; exact c7r558_closed
  · subst row; exact c7r559_closed
  · subst row; exact c7r560_closed
  · subst row; exact c7r561_closed
  · subst row; exact c7r562_closed
  · subst row; exact c7r563_closed
  · subst row; exact c7r564_closed
  · subst row; exact c7r565_closed
  · subst row; exact c7r566_closed
  · subst row; exact c7r567_closed
  · subst row; exact c7r568_closed
  · subst row; exact c7r569_closed
  · subst row; exact c7r570_closed
  · subst row; exact c7r571_closed
  · subst row; exact c7r572_closed
  · subst row; exact c7r573_closed
  · subst row; exact c7r574_closed
  · subst row; exact c7r575_closed
end Polyomino57
