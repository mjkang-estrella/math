import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r384 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)]
def c7r384targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]]
def c7r384choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r384_checked : successorFastRowCheck c7r384targets c7r384 c7r384choice = true := by decide
theorem c7r384_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r384 := by
  refine ⟨c7r384targets, c7r384choice, ?_, c7r384_checked⟩
  intro S h
  simp only [c7r384targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 21 _ (by rfl)))
def c7r385 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)]
def c7r385targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]]
def c7r385choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r385_checked : successorFastRowCheck c7r385targets c7r385 c7r385choice = true := by decide
theorem c7r385_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r385 := by
  refine ⟨c7r385targets, c7r385choice, ?_, c7r385_checked⟩
  intro S h
  simp only [c7r385targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 24 _ (by rfl)))
def c7r386 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)]
def c7r386targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]]
def c7r386choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r386_checked : successorFastRowCheck c7r386targets c7r386 c7r386choice = true := by decide
theorem c7r386_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r386 := by
  refine ⟨c7r386targets, c7r386choice, ?_, c7r386_checked⟩
  intro S h
  simp only [c7r386targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 26 _ (by rfl)))
def c7r387 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)]
def c7r387targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]]
def c7r387choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r387_checked : successorFastRowCheck c7r387targets c7r387 c7r387choice = true := by decide
theorem c7r387_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r387 := by
  refine ⟨c7r387targets, c7r387choice, ?_, c7r387_checked⟩
  intro S h
  simp only [c7r387targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 29 _ (by rfl)))
def c7r388 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)]
def c7r388targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]]
def c7r388choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r388_checked : successorFastRowCheck c7r388targets c7r388 c7r388choice = true := by decide
theorem c7r388_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r388 := by
  refine ⟨c7r388targets, c7r388choice, ?_, c7r388_checked⟩
  intro S h
  simp only [c7r388targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 0 _ (by rfl)))
def c7r389 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)]
def c7r389targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]]
def c7r389choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r389_checked : successorFastRowCheck c7r389targets c7r389 c7r389choice = true := by decide
theorem c7r389_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r389 := by
  refine ⟨c7r389targets, c7r389choice, ?_, c7r389_checked⟩
  intro S h
  simp only [c7r389targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 3 _ (by rfl)))
def c7r390 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)]
def c7r390targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]]
def c7r390choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r390_checked : successorFastRowCheck c7r390targets c7r390 c7r390choice = true := by decide
theorem c7r390_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r390 := by
  refine ⟨c7r390targets, c7r390choice, ?_, c7r390_checked⟩
  intro S h
  simp only [c7r390targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 6 _ (by rfl)))
def c7r391 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)]
def c7r391targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)]]
def c7r391choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r391_checked : successorFastRowCheck c7r391targets c7r391 c7r391choice = true := by decide
theorem c7r391_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r391 := by
  refine ⟨c7r391targets, c7r391choice, ?_, c7r391_checked⟩
  intro S h
  simp only [c7r391targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 11 _ (by rfl)))
def c7r392 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)]
def c7r392targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)]]
def c7r392choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r392_checked : successorFastRowCheck c7r392targets c7r392 c7r392choice = true := by decide
theorem c7r392_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r392 := by
  refine ⟨c7r392targets, c7r392choice, ?_, c7r392_checked⟩
  intro S h
  simp only [c7r392targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 13 _ (by rfl)))
def c7r393 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)]
def c7r393targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]]
def c7r393choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r393_checked : successorFastRowCheck c7r393targets c7r393 c7r393choice = true := by decide
theorem c7r393_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r393 := by
  refine ⟨c7r393targets, c7r393choice, ?_, c7r393_checked⟩
  intro S h
  simp only [c7r393targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 15 _ (by rfl)))
def c7r394 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1)]
def c7r394targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)]]
def c7r394choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r394_checked : successorFastRowCheck c7r394targets c7r394 c7r394choice = true := by decide
theorem c7r394_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r394 := by
  refine ⟨c7r394targets, c7r394choice, ?_, c7r394_checked⟩
  intro S h
  simp only [c7r394targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 18 _ (by rfl)))
def c7r395 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0)]
def c7r395targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)]]
def c7r395choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r395_checked : successorFastRowCheck c7r395targets c7r395 c7r395choice = true := by decide
theorem c7r395_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r395 := by
  refine ⟨c7r395targets, c7r395choice, ?_, c7r395_checked⟩
  intro S h
  simp only [c7r395targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 20 _ (by rfl)))
def c7r396 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3)]
def c7r396targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)]]
def c7r396choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r396_checked : successorFastRowCheck c7r396targets c7r396 c7r396choice = true := by decide
theorem c7r396_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r396 := by
  refine ⟨c7r396targets, c7r396choice, ?_, c7r396_checked⟩
  intro S h
  simp only [c7r396targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 24 _ (by rfl)))
def c7r397 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1)]
def c7r397targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)]]
def c7r397choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r397_checked : successorFastRowCheck c7r397targets c7r397 c7r397choice = true := by decide
theorem c7r397_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r397 := by
  refine ⟨c7r397targets, c7r397choice, ?_, c7r397_checked⟩
  intro S h
  simp only [c7r397targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 27 _ (by rfl)))
def c7r398 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2)]
def c7r398targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]]
def c7r398choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r398_checked : successorFastRowCheck c7r398targets c7r398 c7r398choice = true := by decide
theorem c7r398_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r398 := by
  refine ⟨c7r398targets, c7r398choice, ?_, c7r398_checked⟩
  intro S h
  simp only [c7r398targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 29 _ (by rfl)))
def c7r399 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1)]
def c7r399targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)]]
def c7r399choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r399_checked : successorFastRowCheck c7r399targets c7r399 c7r399choice = true := by decide
theorem c7r399_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r399 := by
  refine ⟨c7r399targets, c7r399choice, ?_, c7r399_checked⟩
  intro S h
  simp only [c7r399targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 0 _ (by rfl)))
def c7r400 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2)]
def c7r400targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)]]
def c7r400choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r400_checked : successorFastRowCheck c7r400targets c7r400 c7r400choice = true := by decide
theorem c7r400_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r400 := by
  refine ⟨c7r400targets, c7r400choice, ?_, c7r400_checked⟩
  intro S h
  simp only [c7r400targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 3 _ (by rfl)))
def c7r401 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1)]
def c7r401targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]]
def c7r401choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r401_checked : successorFastRowCheck c7r401targets c7r401 c7r401choice = true := by decide
theorem c7r401_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r401 := by
  refine ⟨c7r401targets, c7r401choice, ?_, c7r401_checked⟩
  intro S h
  simp only [c7r401targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 6 _ (by rfl)))
def c7r402 : List GridPoint := [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)]
def c7r402targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r402choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r402_checked : successorFastRowCheck c7r402targets c7r402 c7r402choice = true := by decide
theorem c7r402_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r402 := by
  refine ⟨c7r402targets, c7r402choice, ?_, c7r402_checked⟩
  intro S h
  simp only [c7r402targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 11 _ (by rfl)))
def c7r403 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1)]
def c7r403targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
def c7r403choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r403_checked : successorFastRowCheck c7r403targets c7r403 c7r403choice = true := by decide
theorem c7r403_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r403 := by
  refine ⟨c7r403targets, c7r403choice, ?_, c7r403_checked⟩
  intro S h
  simp only [c7r403targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 16 _ (by rfl)))
def c7r404 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)]
def c7r404targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r404choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r404_checked : successorFastRowCheck c7r404targets c7r404 c7r404choice = true := by decide
theorem c7r404_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r404 := by
  refine ⟨c7r404targets, c7r404choice, ?_, c7r404_checked⟩
  intro S h
  simp only [c7r404targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 21 _ (by rfl)))
def c7r405 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0)]
def c7r405targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
def c7r405choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r405_checked : successorFastRowCheck c7r405targets c7r405 c7r405choice = true := by decide
theorem c7r405_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r405 := by
  refine ⟨c7r405targets, c7r405choice, ?_, c7r405_checked⟩
  intro S h
  simp only [c7r405targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 23 _ (by rfl)))
def c7r406 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)]
def c7r406targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
def c7r406choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r406_checked : successorFastRowCheck c7r406targets c7r406 c7r406choice = true := by decide
theorem c7r406_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r406 := by
  refine ⟨c7r406targets, c7r406choice, ?_, c7r406_checked⟩
  intro S h
  simp only [c7r406targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 25 _ (by rfl)))
def c7r407 : List GridPoint := [(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)]
def c7r407targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
def c7r407choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r407_checked : successorFastRowCheck c7r407targets c7r407 c7r407choice = true := by decide
theorem c7r407_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r407 := by
  refine ⟨c7r407targets, c7r407choice, ?_, c7r407_checked⟩
  intro S h
  simp only [c7r407targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 29 _ (by rfl)))
def c7r408 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3)]
def c7r408targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r408choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r408_checked : successorFastRowCheck c7r408targets c7r408 c7r408choice = true := by decide
theorem c7r408_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r408 := by
  refine ⟨c7r408targets, c7r408choice, ?_, c7r408_checked⟩
  intro S h
  simp only [c7r408targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 5 _ (by rfl)))
def c7r409 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0)]
def c7r409targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r409choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r409_checked : successorFastRowCheck c7r409targets c7r409 c7r409choice = true := by decide
theorem c7r409_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r409 := by
  refine ⟨c7r409targets, c7r409choice, ?_, c7r409_checked⟩
  intro S h
  simp only [c7r409targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 8 _ (by rfl)))
def c7r410 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1)]
def c7r410targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r410choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r410_checked : successorFastRowCheck c7r410targets c7r410 c7r410choice = true := by decide
theorem c7r410_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r410 := by
  refine ⟨c7r410targets, c7r410choice, ?_, c7r410_checked⟩
  intro S h
  simp only [c7r410targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 10 _ (by rfl)))
def c7r411 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2)]
def c7r411targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r411choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r411_checked : successorFastRowCheck c7r411targets c7r411 c7r411choice = true := by decide
theorem c7r411_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r411 := by
  refine ⟨c7r411targets, c7r411choice, ?_, c7r411_checked⟩
  intro S h
  simp only [c7r411targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 12 _ (by rfl)))
def c7r412 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1)]
def c7r412targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]]
def c7r412choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r412_checked : successorFastRowCheck c7r412targets c7r412 c7r412choice = true := by decide
theorem c7r412_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r412 := by
  refine ⟨c7r412targets, c7r412choice, ?_, c7r412_checked⟩
  intro S h
  simp only [c7r412targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 15 _ (by rfl)))
def c7r413 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0)]
def c7r413targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]]
def c7r413choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r413_checked : successorFastRowCheck c7r413targets c7r413 c7r413choice = true := by decide
theorem c7r413_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r413 := by
  refine ⟨c7r413targets, c7r413choice, ?_, c7r413_checked⟩
  intro S h
  simp only [c7r413targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 17 _ (by rfl)))
def c7r414 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2)]
def c7r414targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]
def c7r414choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r414_checked : successorFastRowCheck c7r414targets c7r414 c7r414choice = true := by decide
theorem c7r414_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r414 := by
  refine ⟨c7r414targets, c7r414choice, ?_, c7r414_checked⟩
  intro S h
  simp only [c7r414targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 20 _ (by rfl)))
def c7r415 : List GridPoint := [(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1)]
def c7r415targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]]
def c7r415choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r415_checked : successorFastRowCheck c7r415targets c7r415 c7r415choice = true := by decide
theorem c7r415_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r415 := by
  refine ⟨c7r415targets, c7r415choice, ?_, c7r415_checked⟩
  intro S h
  simp only [c7r415targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L62_lift _ (familyLookup_sound F8B000L62 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 23 _ (by rfl)))
theorem C7R00384_closed (row : List GridPoint) (h : FamilyMember row F7B000L12) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L12, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r384_closed
  · subst row; exact c7r385_closed
  · subst row; exact c7r386_closed
  · subst row; exact c7r387_closed
  · subst row; exact c7r388_closed
  · subst row; exact c7r389_closed
  · subst row; exact c7r390_closed
  · subst row; exact c7r391_closed
  · subst row; exact c7r392_closed
  · subst row; exact c7r393_closed
  · subst row; exact c7r394_closed
  · subst row; exact c7r395_closed
  · subst row; exact c7r396_closed
  · subst row; exact c7r397_closed
  · subst row; exact c7r398_closed
  · subst row; exact c7r399_closed
  · subst row; exact c7r400_closed
  · subst row; exact c7r401_closed
  · subst row; exact c7r402_closed
  · subst row; exact c7r403_closed
  · subst row; exact c7r404_closed
  · subst row; exact c7r405_closed
  · subst row; exact c7r406_closed
  · subst row; exact c7r407_closed
  · subst row; exact c7r408_closed
  · subst row; exact c7r409_closed
  · subst row; exact c7r410_closed
  · subst row; exact c7r411_closed
  · subst row; exact c7r412_closed
  · subst row; exact c7r413_closed
  · subst row; exact c7r414_closed
  · subst row; exact c7r415_closed
end Polyomino57
