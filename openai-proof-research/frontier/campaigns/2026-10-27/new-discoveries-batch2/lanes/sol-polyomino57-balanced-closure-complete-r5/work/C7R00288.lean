import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r288 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)]
def c7r288targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)]]
def c7r288choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r288_checked : successorFastRowCheck c7r288targets c7r288 c7r288choice = true := by decide
theorem c7r288_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r288 := by
  refine ⟨c7r288targets, c7r288choice, ?_, c7r288_checked⟩
  intro S h
  simp only [c7r288targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 18 _ (by rfl)))
def c7r289 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)]
def c7r289targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)]]
def c7r289choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r289_checked : successorFastRowCheck c7r289targets c7r289 c7r289choice = true := by decide
theorem c7r289_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r289 := by
  refine ⟨c7r289targets, c7r289choice, ?_, c7r289_checked⟩
  intro S h
  simp only [c7r289targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 20 _ (by rfl)))
def c7r290 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)]
def c7r290targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)]]
def c7r290choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r290_checked : successorFastRowCheck c7r290targets c7r290 c7r290choice = true := by decide
theorem c7r290_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r290 := by
  refine ⟨c7r290targets, c7r290choice, ?_, c7r290_checked⟩
  intro S h
  simp only [c7r290targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 23 _ (by rfl)))
def c7r291 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)]
def c7r291targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)]]
def c7r291choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r291_checked : successorFastRowCheck c7r291targets c7r291 c7r291choice = true := by decide
theorem c7r291_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r291 := by
  refine ⟨c7r291targets, c7r291choice, ?_, c7r291_checked⟩
  intro S h
  simp only [c7r291targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 25 _ (by rfl)))
def c7r292 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)]
def c7r292targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)]]
def c7r292choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r292_checked : successorFastRowCheck c7r292targets c7r292 c7r292choice = true := by decide
theorem c7r292_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r292 := by
  refine ⟨c7r292targets, c7r292choice, ?_, c7r292_checked⟩
  intro S h
  simp only [c7r292targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 30 _ (by rfl)))
def c7r293 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)]
def c7r293targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)]]
def c7r293choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r293_checked : successorFastRowCheck c7r293targets c7r293 c7r293choice = true := by decide
theorem c7r293_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r293 := by
  refine ⟨c7r293targets, c7r293choice, ?_, c7r293_checked⟩
  intro S h
  simp only [c7r293targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 2 _ (by rfl)))
def c7r294 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)]
def c7r294targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)]]
def c7r294choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r294_checked : successorFastRowCheck c7r294targets c7r294 c7r294choice = true := by decide
theorem c7r294_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r294 := by
  refine ⟨c7r294targets, c7r294choice, ?_, c7r294_checked⟩
  intro S h
  simp only [c7r294targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 4 _ (by rfl)))
def c7r295 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)]
def c7r295targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)]]
def c7r295choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r295_checked : successorFastRowCheck c7r295targets c7r295 c7r295choice = true := by decide
theorem c7r295_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r295 := by
  refine ⟨c7r295targets, c7r295choice, ?_, c7r295_checked⟩
  intro S h
  simp only [c7r295targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 6 _ (by rfl)))
def c7r296 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)]
def c7r296targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r296choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r296_checked : successorFastRowCheck c7r296targets c7r296 c7r296choice = true := by decide
theorem c7r296_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r296 := by
  refine ⟨c7r296targets, c7r296choice, ?_, c7r296_checked⟩
  intro S h
  simp only [c7r296targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 9 _ (by rfl)))
def c7r297 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)]
def c7r297targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)]]
def c7r297choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r297_checked : successorFastRowCheck c7r297targets c7r297 c7r297choice = true := by decide
theorem c7r297_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r297 := by
  refine ⟨c7r297targets, c7r297choice, ?_, c7r297_checked⟩
  intro S h
  simp only [c7r297targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 12 _ (by rfl)))
def c7r298 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)]
def c7r298targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)]]
def c7r298choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r298_checked : successorFastRowCheck c7r298targets c7r298 c7r298choice = true := by decide
theorem c7r298_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r298 := by
  refine ⟨c7r298targets, c7r298choice, ?_, c7r298_checked⟩
  intro S h
  simp only [c7r298targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 15 _ (by rfl)))
def c7r299 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)]
def c7r299targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)]]
def c7r299choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,4),(8,(0,0))),((4,2),(9,(0,0))),((4,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r299_checked : successorFastRowCheck c7r299targets c7r299 c7r299choice = true := by decide
theorem c7r299_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r299 := by
  refine ⟨c7r299targets, c7r299choice, ?_, c7r299_checked⟩
  intro S h
  simp only [c7r299targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 18 _ (by rfl)))
def c7r300 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]
def c7r300targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)]]
def c7r300choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r300_checked : successorFastRowCheck c7r300targets c7r300 c7r300choice = true := by decide
theorem c7r300_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r300 := by
  refine ⟨c7r300targets, c7r300choice, ?_, c7r300_checked⟩
  intro S h
  simp only [c7r300targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 21 _ (by rfl)))
def c7r301 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)]
def c7r301targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]]
def c7r301choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r301_checked : successorFastRowCheck c7r301targets c7r301 c7r301choice = true := by decide
theorem c7r301_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r301 := by
  refine ⟨c7r301targets, c7r301choice, ?_, c7r301_checked⟩
  intro S h
  simp only [c7r301targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 26 _ (by rfl)))
def c7r302 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)]
def c7r302targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]]
def c7r302choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r302_checked : successorFastRowCheck c7r302targets c7r302 c7r302choice = true := by decide
theorem c7r302_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r302 := by
  refine ⟨c7r302targets, c7r302choice, ?_, c7r302_checked⟩
  intro S h
  simp only [c7r302targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 28 _ (by rfl)))
def c7r303 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)]
def c7r303targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]
def c7r303choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r303_checked : successorFastRowCheck c7r303targets c7r303 c7r303choice = true := by decide
theorem c7r303_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r303 := by
  refine ⟨c7r303targets, c7r303choice, ?_, c7r303_checked⟩
  intro S h
  simp only [c7r303targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 30 _ (by rfl)))
def c7r304 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)]
def c7r304targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)]]
def c7r304choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r304_checked : successorFastRowCheck c7r304targets c7r304 c7r304choice = true := by decide
theorem c7r304_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r304 := by
  refine ⟨c7r304targets, c7r304choice, ?_, c7r304_checked⟩
  intro S h
  simp only [c7r304targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 2 _ (by rfl)))
def c7r305 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)]
def c7r305targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)]]
def c7r305choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r305_checked : successorFastRowCheck c7r305targets c7r305 c7r305choice = true := by decide
theorem c7r305_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r305 := by
  refine ⟨c7r305targets, c7r305choice, ?_, c7r305_checked⟩
  intro S h
  simp only [c7r305targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 5 _ (by rfl)))
def c7r306 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)]
def c7r306targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)]]
def c7r306choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r306_checked : successorFastRowCheck c7r306targets c7r306 c7r306choice = true := by decide
theorem c7r306_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r306 := by
  refine ⟨c7r306targets, c7r306choice, ?_, c7r306_checked⟩
  intro S h
  simp only [c7r306targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 7 _ (by rfl)))
def c7r307 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)]
def c7r307targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]]
def c7r307choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r307_checked : successorFastRowCheck c7r307targets c7r307 c7r307choice = true := by decide
theorem c7r307_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r307 := by
  refine ⟨c7r307targets, c7r307choice, ?_, c7r307_checked⟩
  intro S h
  simp only [c7r307targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 10 _ (by rfl)))
def c7r308 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)]
def c7r308targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)]]
def c7r308choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r308_checked : successorFastRowCheck c7r308targets c7r308 c7r308choice = true := by decide
theorem c7r308_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r308 := by
  refine ⟨c7r308targets, c7r308choice, ?_, c7r308_checked⟩
  intro S h
  simp only [c7r308targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 13 _ (by rfl)))
def c7r309 : List GridPoint := [(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]
def c7r309targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)]]
def c7r309choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r309_checked : successorFastRowCheck c7r309targets c7r309 c7r309choice = true := by decide
theorem c7r309_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r309 := by
  refine ⟨c7r309targets, c7r309choice, ?_, c7r309_checked⟩
  intro S h
  simp only [c7r309targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 16 _ (by rfl)))
def c7r310 : List GridPoint := [(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)]
def c7r310targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
def c7r310choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r310_checked : successorFastRowCheck c7r310targets c7r310 c7r310choice = true := by decide
theorem c7r310_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r310 := by
  refine ⟨c7r310targets, c7r310choice, ?_, c7r310_checked⟩
  intro S h
  simp only [c7r310targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 21 _ (by rfl)))
def c7r311 : List GridPoint := [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)]
def c7r311targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r311choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r311_checked : successorFastRowCheck c7r311targets c7r311 c7r311choice = true := by decide
theorem c7r311_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r311 := by
  refine ⟨c7r311targets, c7r311choice, ?_, c7r311_checked⟩
  intro S h
  simp only [c7r311targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 26 _ (by rfl)))
def c7r312 : List GridPoint := [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)]
def c7r312targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r312choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r312_checked : successorFastRowCheck c7r312targets c7r312 c7r312choice = true := by decide
theorem c7r312_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r312 := by
  refine ⟨c7r312targets, c7r312choice, ?_, c7r312_checked⟩
  intro S h
  simp only [c7r312targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 29 _ (by rfl)))
def c7r313 : List GridPoint := [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)]
def c7r313targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r313choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r313_checked : successorFastRowCheck c7r313targets c7r313 c7r313choice = true := by decide
theorem c7r313_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r313 := by
  refine ⟨c7r313targets, c7r313choice, ?_, c7r313_checked⟩
  intro S h
  simp only [c7r313targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 31 _ (by rfl)))
def c7r314 : List GridPoint := [(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]
def c7r314targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r314choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r314_checked : successorFastRowCheck c7r314targets c7r314 c7r314choice = true := by decide
theorem c7r314_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r314 := by
  refine ⟨c7r314targets, c7r314choice, ?_, c7r314_checked⟩
  intro S h
  simp only [c7r314targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 1 _ (by rfl)))
def c7r315 : List GridPoint := [(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)]
def c7r315targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r315choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r315_checked : successorFastRowCheck c7r315targets c7r315 c7r315choice = true := by decide
theorem c7r315_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r315 := by
  refine ⟨c7r315targets, c7r315choice, ?_, c7r315_checked⟩
  intro S h
  simp only [c7r315targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 8 _ (by rfl)))
def c7r316 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)]
def c7r316targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
def c7r316choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,5),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r316_checked : successorFastRowCheck c7r316targets c7r316 c7r316choice = true := by decide
theorem c7r316_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r316 := by
  refine ⟨c7r316targets, c7r316choice, ?_, c7r316_checked⟩
  intro S h
  simp only [c7r316targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 15 _ (by rfl)))
def c7r317 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)]
def c7r317targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
def c7r317choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r317_checked : successorFastRowCheck c7r317targets c7r317 c7r317choice = true := by decide
theorem c7r317_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r317 := by
  refine ⟨c7r317targets, c7r317choice, ?_, c7r317_checked⟩
  intro S h
  simp only [c7r317targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 19 _ (by rfl)))
def c7r318 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)]
def c7r318targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
def c7r318choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r318_checked : successorFastRowCheck c7r318targets c7r318 c7r318choice = true := by decide
theorem c7r318_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r318 := by
  refine ⟨c7r318targets, c7r318choice, ?_, c7r318_checked⟩
  intro S h
  simp only [c7r318targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 22 _ (by rfl)))
def c7r319 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)]
def c7r319targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
def c7r319choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r319_checked : successorFastRowCheck c7r319targets c7r319 c7r319choice = true := by decide
theorem c7r319_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r319 := by
  refine ⟨c7r319targets, c7r319choice, ?_, c7r319_checked⟩
  intro S h
  simp only [c7r319targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 24 _ (by rfl)))
theorem C7R00288_closed (row : List GridPoint) (h : FamilyMember row F7B000L9) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L9, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r288_closed
  · subst row; exact c7r289_closed
  · subst row; exact c7r290_closed
  · subst row; exact c7r291_closed
  · subst row; exact c7r292_closed
  · subst row; exact c7r293_closed
  · subst row; exact c7r294_closed
  · subst row; exact c7r295_closed
  · subst row; exact c7r296_closed
  · subst row; exact c7r297_closed
  · subst row; exact c7r298_closed
  · subst row; exact c7r299_closed
  · subst row; exact c7r300_closed
  · subst row; exact c7r301_closed
  · subst row; exact c7r302_closed
  · subst row; exact c7r303_closed
  · subst row; exact c7r304_closed
  · subst row; exact c7r305_closed
  · subst row; exact c7r306_closed
  · subst row; exact c7r307_closed
  · subst row; exact c7r308_closed
  · subst row; exact c7r309_closed
  · subst row; exact c7r310_closed
  · subst row; exact c7r311_closed
  · subst row; exact c7r312_closed
  · subst row; exact c7r313_closed
  · subst row; exact c7r314_closed
  · subst row; exact c7r315_closed
  · subst row; exact c7r316_closed
  · subst row; exact c7r317_closed
  · subst row; exact c7r318_closed
  · subst row; exact c7r319_closed
end Polyomino57
