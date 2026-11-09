import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r480 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)]
def c7r480targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]
def c7r480choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r480_checked : successorFastRowCheck c7r480targets c7r480 c7r480choice = true := by decide
theorem c7r480_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r480 := by
  refine ⟨c7r480targets, c7r480choice, ?_, c7r480_checked⟩
  intro S h
  simp only [c7r480targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 2 _ (by rfl)))
def c7r481 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]
def c7r481targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]]
def c7r481choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r481_checked : successorFastRowCheck c7r481targets c7r481 c7r481choice = true := by decide
theorem c7r481_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r481 := by
  refine ⟨c7r481targets, c7r481choice, ?_, c7r481_checked⟩
  intro S h
  simp only [c7r481targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 5 _ (by rfl)))
def c7r482 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)]
def c7r482targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)]]
def c7r482choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r482_checked : successorFastRowCheck c7r482targets c7r482 c7r482choice = true := by decide
theorem c7r482_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r482 := by
  refine ⟨c7r482targets, c7r482choice, ?_, c7r482_checked⟩
  intro S h
  simp only [c7r482targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 10 _ (by rfl)))
def c7r483 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)]
def c7r483targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)]]
def c7r483choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r483_checked : successorFastRowCheck c7r483targets c7r483 c7r483choice = true := by decide
theorem c7r483_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r483 := by
  refine ⟨c7r483targets, c7r483choice, ?_, c7r483_checked⟩
  intro S h
  simp only [c7r483targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 12 _ (by rfl)))
def c7r484 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)]
def c7r484targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)]]
def c7r484choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r484_checked : successorFastRowCheck c7r484targets c7r484 c7r484choice = true := by decide
theorem c7r484_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r484 := by
  refine ⟨c7r484targets, c7r484choice, ?_, c7r484_checked⟩
  intro S h
  simp only [c7r484targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 14 _ (by rfl)))
def c7r485 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)]
def c7r485targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)]]
def c7r485choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r485_checked : successorFastRowCheck c7r485targets c7r485 c7r485choice = true := by decide
theorem c7r485_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r485 := by
  refine ⟨c7r485targets, c7r485choice, ?_, c7r485_checked⟩
  intro S h
  simp only [c7r485targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 17 _ (by rfl)))
def c7r486 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)]
def c7r486targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)]]
def c7r486choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r486_checked : successorFastRowCheck c7r486targets c7r486 c7r486choice = true := by decide
theorem c7r486_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r486 := by
  refine ⟨c7r486targets, c7r486choice, ?_, c7r486_checked⟩
  intro S h
  simp only [c7r486targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 19 _ (by rfl)))
def c7r487 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)]
def c7r487targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)]]
def c7r487choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,5),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r487_checked : successorFastRowCheck c7r487targets c7r487 c7r487choice = true := by decide
theorem c7r487_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r487 := by
  refine ⟨c7r487targets, c7r487choice, ?_, c7r487_checked⟩
  intro S h
  simp only [c7r487targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 24 _ (by rfl)))
def c7r488 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)]
def c7r488targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)]]
def c7r488choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r488_checked : successorFastRowCheck c7r488targets c7r488 c7r488choice = true := by decide
theorem c7r488_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r488 := by
  refine ⟨c7r488targets, c7r488choice, ?_, c7r488_checked⟩
  intro S h
  simp only [c7r488targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 28 _ (by rfl)))
def c7r489 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)]
def c7r489targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)]]
def c7r489choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r489_checked : successorFastRowCheck c7r489targets c7r489 c7r489choice = true := by decide
theorem c7r489_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r489 := by
  refine ⟨c7r489targets, c7r489choice, ?_, c7r489_checked⟩
  intro S h
  simp only [c7r489targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 30 _ (by rfl)))
def c7r490 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)]
def c7r490targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)]]
def c7r490choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r490_checked : successorFastRowCheck c7r490targets c7r490 c7r490choice = true := by decide
theorem c7r490_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r490 := by
  refine ⟨c7r490targets, c7r490choice, ?_, c7r490_checked⟩
  intro S h
  simp only [c7r490targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 0 _ (by rfl)))
def c7r491 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)]
def c7r491targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r491choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r491_checked : successorFastRowCheck c7r491targets c7r491 c7r491choice = true := by decide
theorem c7r491_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r491 := by
  refine ⟨c7r491targets, c7r491choice, ?_, c7r491_checked⟩
  intro S h
  simp only [c7r491targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 3 _ (by rfl)))
def c7r492 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)]
def c7r492targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)]]
def c7r492choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r492_checked : successorFastRowCheck c7r492targets c7r492 c7r492choice = true := by decide
theorem c7r492_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r492 := by
  refine ⟨c7r492targets, c7r492choice, ?_, c7r492_checked⟩
  intro S h
  simp only [c7r492targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 6 _ (by rfl)))
def c7r493 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)]
def c7r493targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)]]
def c7r493choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r493_checked : successorFastRowCheck c7r493targets c7r493 c7r493choice = true := by decide
theorem c7r493_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r493 := by
  refine ⟨c7r493targets, c7r493choice, ?_, c7r493_checked⟩
  intro S h
  simp only [c7r493targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 9 _ (by rfl)))
def c7r494 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)]
def c7r494targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)]]
def c7r494choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,4),(8,(0,0))),((4,2),(9,(0,0))),((4,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r494_checked : successorFastRowCheck c7r494targets c7r494 c7r494choice = true := by decide
theorem c7r494_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r494 := by
  refine ⟨c7r494targets, c7r494choice, ?_, c7r494_checked⟩
  intro S h
  simp only [c7r494targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 12 _ (by rfl)))
def c7r495 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)]
def c7r495targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)]]
def c7r495choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r495_checked : successorFastRowCheck c7r495targets c7r495 c7r495choice = true := by decide
theorem c7r495_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r495 := by
  refine ⟨c7r495targets, c7r495choice, ?_, c7r495_checked⟩
  intro S h
  simp only [c7r495targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 15 _ (by rfl)))
def c7r496 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)]
def c7r496targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]]
def c7r496choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r496_checked : successorFastRowCheck c7r496targets c7r496 c7r496choice = true := by decide
theorem c7r496_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r496 := by
  refine ⟨c7r496targets, c7r496choice, ?_, c7r496_checked⟩
  intro S h
  simp only [c7r496targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 20 _ (by rfl)))
def c7r497 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)]
def c7r497targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]]
def c7r497choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r497_checked : successorFastRowCheck c7r497targets c7r497 c7r497choice = true := by decide
theorem c7r497_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r497 := by
  refine ⟨c7r497targets, c7r497choice, ?_, c7r497_checked⟩
  intro S h
  simp only [c7r497targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 22 _ (by rfl)))
def c7r498 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)]
def c7r498targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]
def c7r498choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r498_checked : successorFastRowCheck c7r498targets c7r498 c7r498choice = true := by decide
theorem c7r498_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r498 := by
  refine ⟨c7r498targets, c7r498choice, ?_, c7r498_checked⟩
  intro S h
  simp only [c7r498targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 24 _ (by rfl)))
def c7r499 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)]
def c7r499targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)]]
def c7r499choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r499_checked : successorFastRowCheck c7r499targets c7r499 c7r499choice = true := by decide
theorem c7r499_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r499 := by
  refine ⟨c7r499targets, c7r499choice, ?_, c7r499_checked⟩
  intro S h
  simp only [c7r499targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 28 _ (by rfl)))
def c7r500 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)]
def c7r500targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)]]
def c7r500choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r500_checked : successorFastRowCheck c7r500targets c7r500 c7r500choice = true := by decide
theorem c7r500_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r500 := by
  refine ⟨c7r500targets, c7r500choice, ?_, c7r500_checked⟩
  intro S h
  simp only [c7r500targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 31 _ (by rfl)))
def c7r501 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)]
def c7r501targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)]]
def c7r501choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r501_checked : successorFastRowCheck c7r501targets c7r501 c7r501choice = true := by decide
theorem c7r501_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r501 := by
  refine ⟨c7r501targets, c7r501choice, ?_, c7r501_checked⟩
  intro S h
  simp only [c7r501targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 1 _ (by rfl)))
def c7r502 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)]
def c7r502targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]]
def c7r502choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r502_checked : successorFastRowCheck c7r502targets c7r502 c7r502choice = true := by decide
theorem c7r502_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r502 := by
  refine ⟨c7r502targets, c7r502choice, ?_, c7r502_checked⟩
  intro S h
  simp only [c7r502targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 4 _ (by rfl)))
def c7r503 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)]
def c7r503targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)]]
def c7r503choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r503_checked : successorFastRowCheck c7r503targets c7r503 c7r503choice = true := by decide
theorem c7r503_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r503 := by
  refine ⟨c7r503targets, c7r503choice, ?_, c7r503_checked⟩
  intro S h
  simp only [c7r503targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 7 _ (by rfl)))
def c7r504 : List GridPoint := [(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)]
def c7r504targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)]]
def c7r504choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r504_checked : successorFastRowCheck c7r504targets c7r504 c7r504choice = true := by decide
theorem c7r504_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r504 := by
  refine ⟨c7r504targets, c7r504choice, ?_, c7r504_checked⟩
  intro S h
  simp only [c7r504targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 10 _ (by rfl)))
def c7r505 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)]
def c7r505targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
def c7r505choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,5),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r505_checked : successorFastRowCheck c7r505targets c7r505 c7r505choice = true := by decide
theorem c7r505_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r505 := by
  refine ⟨c7r505targets, c7r505choice, ?_, c7r505_checked⟩
  intro S h
  simp only [c7r505targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 16 _ (by rfl)))
def c7r506 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)]
def c7r506targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
def c7r506choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r506_checked : successorFastRowCheck c7r506targets c7r506 c7r506choice = true := by decide
theorem c7r506_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r506 := by
  refine ⟨c7r506targets, c7r506choice, ?_, c7r506_checked⟩
  intro S h
  simp only [c7r506targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 21 _ (by rfl)))
def c7r507 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)]
def c7r507targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]
def c7r507choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r507_checked : successorFastRowCheck c7r507targets c7r507 c7r507choice = true := by decide
theorem c7r507_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r507 := by
  refine ⟨c7r507targets, c7r507choice, ?_, c7r507_checked⟩
  intro S h
  simp only [c7r507targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 25 _ (by rfl)))
def c7r508 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)]
def c7r508targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)]]
def c7r508choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r508_checked : successorFastRowCheck c7r508targets c7r508 c7r508choice = true := by decide
theorem c7r508_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r508 := by
  refine ⟨c7r508targets, c7r508choice, ?_, c7r508_checked⟩
  intro S h
  simp only [c7r508targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 27 _ (by rfl)))
def c7r509 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]
def c7r509targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)]]
def c7r509choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r509_checked : successorFastRowCheck c7r509targets c7r509 c7r509choice = true := by decide
theorem c7r509_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r509 := by
  refine ⟨c7r509targets, c7r509choice, ?_, c7r509_checked⟩
  intro S h
  simp only [c7r509targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 29 _ (by rfl)))
def c7r510 : List GridPoint := [(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)]
def c7r510targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)]]
def c7r510choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,0),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r510_checked : successorFastRowCheck c7r510targets c7r510 c7r510choice = true := by decide
theorem c7r510_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r510 := by
  refine ⟨c7r510targets, c7r510choice, ?_, c7r510_checked⟩
  intro S h
  simp only [c7r510targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 2 _ (by rfl)))
def c7r511 : List GridPoint := [(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)]
def c7r511targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r511choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,0),(3,(0,0))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,4),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r511_checked : successorFastRowCheck c7r511targets c7r511 c7r511choice = true := by decide
theorem c7r511_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r511 := by
  refine ⟨c7r511targets, c7r511choice, ?_, c7r511_checked⟩
  intro S h
  simp only [c7r511targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L6_lift _ (familyLookup_sound F8B001L6 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 9 _ (by rfl)))
theorem C7R00480_closed (row : List GridPoint) (h : FamilyMember row F7B000L15) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L15, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r480_closed
  · subst row; exact c7r481_closed
  · subst row; exact c7r482_closed
  · subst row; exact c7r483_closed
  · subst row; exact c7r484_closed
  · subst row; exact c7r485_closed
  · subst row; exact c7r486_closed
  · subst row; exact c7r487_closed
  · subst row; exact c7r488_closed
  · subst row; exact c7r489_closed
  · subst row; exact c7r490_closed
  · subst row; exact c7r491_closed
  · subst row; exact c7r492_closed
  · subst row; exact c7r493_closed
  · subst row; exact c7r494_closed
  · subst row; exact c7r495_closed
  · subst row; exact c7r496_closed
  · subst row; exact c7r497_closed
  · subst row; exact c7r498_closed
  · subst row; exact c7r499_closed
  · subst row; exact c7r500_closed
  · subst row; exact c7r501_closed
  · subst row; exact c7r502_closed
  · subst row; exact c7r503_closed
  · subst row; exact c7r504_closed
  · subst row; exact c7r505_closed
  · subst row; exact c7r506_closed
  · subst row; exact c7r507_closed
  · subst row; exact c7r508_closed
  · subst row; exact c7r509_closed
  · subst row; exact c7r510_closed
  · subst row; exact c7r511_closed
end Polyomino57
