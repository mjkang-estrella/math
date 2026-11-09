import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r608 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]
def c7r608targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
def c7r608choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r608_checked : successorFastRowCheck c7r608targets c7r608 c7r608choice = true := by decide
theorem c7r608_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r608 := by
  refine ⟨c7r608targets, c7r608choice, ?_, c7r608_checked⟩
  intro S h
  simp only [c7r608targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 25 _ (by rfl)))
def c7r609 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)]
def c7r609targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
def c7r609choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r609_checked : successorFastRowCheck c7r609targets c7r609 c7r609choice = true := by decide
theorem c7r609_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r609 := by
  refine ⟨c7r609targets, c7r609choice, ?_, c7r609_checked⟩
  intro S h
  simp only [c7r609targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 28 _ (by rfl)))
def c7r610 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)]
def c7r610targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
def c7r610choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,0),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r610_checked : successorFastRowCheck c7r610targets c7r610 c7r610choice = true := by decide
theorem c7r610_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r610 := by
  refine ⟨c7r610targets, c7r610choice, ?_, c7r610_checked⟩
  intro S h
  simp only [c7r610targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 31 _ (by rfl)))
def c7r611 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]
def c7r611targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
def c7r611choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r611_checked : successorFastRowCheck c7r611targets c7r611 c7r611choice = true := by decide
theorem c7r611_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r611 := by
  refine ⟨c7r611targets, c7r611choice, ?_, c7r611_checked⟩
  intro S h
  simp only [c7r611targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 1 _ (by rfl)))
def c7r612 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]
def c7r612targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
def c7r612choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r612_checked : successorFastRowCheck c7r612targets c7r612 c7r612choice = true := by decide
theorem c7r612_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r612 := by
  refine ⟨c7r612targets, c7r612choice, ?_, c7r612_checked⟩
  intro S h
  simp only [c7r612targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 4 _ (by rfl)))
def c7r613 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)]
def c7r613targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
def c7r613choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r613_checked : successorFastRowCheck c7r613targets c7r613 c7r613choice = true := by decide
theorem c7r613_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r613 := by
  refine ⟨c7r613targets, c7r613choice, ?_, c7r613_checked⟩
  intro S h
  simp only [c7r613targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L7_lift _ (familyLookup_sound F8B001L7 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 7 _ (by rfl)))
def c7r614 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]
def c7r614targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
def c7r614choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r614_checked : successorFastRowCheck c7r614targets c7r614 c7r614choice = true := by decide
theorem c7r614_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r614 := by
  refine ⟨c7r614targets, c7r614choice, ?_, c7r614_checked⟩
  intro S h
  simp only [c7r614targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 10 _ (by rfl)))
def c7r615 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)]
def c7r615targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
def c7r615choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r615_checked : successorFastRowCheck c7r615targets c7r615 c7r615choice = true := by decide
theorem c7r615_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r615 := by
  refine ⟨c7r615targets, c7r615choice, ?_, c7r615_checked⟩
  intro S h
  simp only [c7r615targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 13 _ (by rfl)))
def c7r616 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]
def c7r616targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
def c7r616choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r616_checked : successorFastRowCheck c7r616targets c7r616 c7r616choice = true := by decide
theorem c7r616_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r616 := by
  refine ⟨c7r616targets, c7r616choice, ?_, c7r616_checked⟩
  intro S h
  simp only [c7r616targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 16 _ (by rfl)))
def c7r617 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)]
def c7r617targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
def c7r617choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r617_checked : successorFastRowCheck c7r617targets c7r617 c7r617choice = true := by decide
theorem c7r617_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r617 := by
  refine ⟨c7r617targets, c7r617choice, ?_, c7r617_checked⟩
  intro S h
  simp only [c7r617targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 19 _ (by rfl)))
def c7r618 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]
def c7r618targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
def c7r618choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r618_checked : successorFastRowCheck c7r618targets c7r618 c7r618choice = true := by decide
theorem c7r618_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r618 := by
  refine ⟨c7r618targets, c7r618choice, ?_, c7r618_checked⟩
  intro S h
  simp only [c7r618targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 22 _ (by rfl)))
def c7r619 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
def c7r619targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r619choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r619_checked : successorFastRowCheck c7r619targets c7r619 c7r619choice = true := by decide
theorem c7r619_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r619 := by
  refine ⟨c7r619targets, c7r619choice, ?_, c7r619_checked⟩
  intro S h
  simp only [c7r619targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 27 _ (by rfl)))
def c7r620 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)]
def c7r620targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
def c7r620choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r620_checked : successorFastRowCheck c7r620targets c7r620 c7r620choice = true := by decide
theorem c7r620_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r620 := by
  refine ⟨c7r620targets, c7r620choice, ?_, c7r620_checked⟩
  intro S h
  simp only [c7r620targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 29 _ (by rfl)))
def c7r621 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]
def c7r621targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
def c7r621choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r621_checked : successorFastRowCheck c7r621targets c7r621 c7r621choice = true := by decide
theorem c7r621_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r621 := by
  refine ⟨c7r621targets, c7r621choice, ?_, c7r621_checked⟩
  intro S h
  simp only [c7r621targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 31 _ (by rfl)))
def c7r622 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)]
def c7r622targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)]]
def c7r622choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r622_checked : successorFastRowCheck c7r622targets c7r622 c7r622choice = true := by decide
theorem c7r622_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r622 := by
  refine ⟨c7r622targets, c7r622choice, ?_, c7r622_checked⟩
  intro S h
  simp only [c7r622targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 3 _ (by rfl)))
def c7r623 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)]
def c7r623targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)]]
def c7r623choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r623_checked : successorFastRowCheck c7r623targets c7r623 c7r623choice = true := by decide
theorem c7r623_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r623 := by
  refine ⟨c7r623targets, c7r623choice, ?_, c7r623_checked⟩
  intro S h
  simp only [c7r623targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 6 _ (by rfl)))
def c7r624 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]
def c7r624targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)]]
def c7r624choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r624_checked : successorFastRowCheck c7r624targets c7r624 c7r624choice = true := by decide
theorem c7r624_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r624 := by
  refine ⟨c7r624targets, c7r624choice, ?_, c7r624_checked⟩
  intro S h
  simp only [c7r624targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 9 _ (by rfl)))
def c7r625 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)]
def c7r625targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)]]
def c7r625choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r625_checked : successorFastRowCheck c7r625targets c7r625 c7r625choice = true := by decide
theorem c7r625_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r625 := by
  refine ⟨c7r625targets, c7r625choice, ?_, c7r625_checked⟩
  intro S h
  simp only [c7r625targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 12 _ (by rfl)))
def c7r626 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]
def c7r626targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)]]
def c7r626choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r626_checked : successorFastRowCheck c7r626targets c7r626 c7r626choice = true := by decide
theorem c7r626_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r626 := by
  refine ⟨c7r626targets, c7r626choice, ?_, c7r626_checked⟩
  intro S h
  simp only [c7r626targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 14 _ (by rfl)))
def c7r627 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)]
def c7r627targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)]]
def c7r627choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r627_checked : successorFastRowCheck c7r627targets c7r627 c7r627choice = true := by decide
theorem c7r627_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r627 := by
  refine ⟨c7r627targets, c7r627choice, ?_, c7r627_checked⟩
  intro S h
  simp only [c7r627targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 18 _ (by rfl)))
def c7r628 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)]
def c7r628targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]
def c7r628choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r628_checked : successorFastRowCheck c7r628targets c7r628 c7r628choice = true := by decide
theorem c7r628_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r628 := by
  refine ⟨c7r628targets, c7r628choice, ?_, c7r628_checked⟩
  intro S h
  simp only [c7r628targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 21 _ (by rfl)))
def c7r629 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]
def c7r629targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]
def c7r629choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r629_checked : successorFastRowCheck c7r629targets c7r629 c7r629choice = true := by decide
theorem c7r629_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r629 := by
  refine ⟨c7r629targets, c7r629choice, ?_, c7r629_checked⟩
  intro S h
  simp only [c7r629targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 23 _ (by rfl)))
def c7r630 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)]
def c7r630targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
def c7r630choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r630_checked : successorFastRowCheck c7r630targets c7r630 c7r630choice = true := by decide
theorem c7r630_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r630 := by
  refine ⟨c7r630targets, c7r630choice, ?_, c7r630_checked⟩
  intro S h
  simp only [c7r630targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 26 _ (by rfl)))
def c7r631 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)]
def c7r631targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]
def c7r631choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r631_checked : successorFastRowCheck c7r631targets c7r631 c7r631choice = true := by decide
theorem c7r631_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r631 := by
  refine ⟨c7r631targets, c7r631choice, ?_, c7r631_checked⟩
  intro S h
  simp only [c7r631targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 29 _ (by rfl)))
def c7r632 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]
def c7r632targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)]]
def c7r632choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r632_checked : successorFastRowCheck c7r632targets c7r632 c7r632choice = true := by decide
theorem c7r632_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r632 := by
  refine ⟨c7r632targets, c7r632choice, ?_, c7r632_checked⟩
  intro S h
  simp only [c7r632targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 0 _ (by rfl)))
def c7r633 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)]
def c7r633targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)]]
def c7r633choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r633_checked : successorFastRowCheck c7r633targets c7r633 c7r633choice = true := by decide
theorem c7r633_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r633 := by
  refine ⟨c7r633targets, c7r633choice, ?_, c7r633_checked⟩
  intro S h
  simp only [c7r633targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 4 _ (by rfl)))
def c7r634 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)]
def c7r634targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]
def c7r634choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r634_checked : successorFastRowCheck c7r634targets c7r634 c7r634choice = true := by decide
theorem c7r634_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r634 := by
  refine ⟨c7r634targets, c7r634choice, ?_, c7r634_checked⟩
  intro S h
  simp only [c7r634targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 7 _ (by rfl)))
def c7r635 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]
def c7r635targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)]]
def c7r635choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r635_checked : successorFastRowCheck c7r635targets c7r635 c7r635choice = true := by decide
theorem c7r635_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r635 := by
  refine ⟨c7r635targets, c7r635choice, ?_, c7r635_checked⟩
  intro S h
  simp only [c7r635targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 9 _ (by rfl)))
def c7r636 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)]
def c7r636targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]
def c7r636choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r636_checked : successorFastRowCheck c7r636targets c7r636 c7r636choice = true := by decide
theorem c7r636_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r636 := by
  refine ⟨c7r636targets, c7r636choice, ?_, c7r636_checked⟩
  intro S h
  simp only [c7r636targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 13 _ (by rfl)))
def c7r637 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)]
def c7r637targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)]]
def c7r637choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r637_checked : successorFastRowCheck c7r637targets c7r637 c7r637choice = true := by decide
theorem c7r637_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r637 := by
  refine ⟨c7r637targets, c7r637choice, ?_, c7r637_checked⟩
  intro S h
  simp only [c7r637targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 16 _ (by rfl)))
def c7r638 : List GridPoint := [(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]
def c7r638targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)]]
def c7r638choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r638_checked : successorFastRowCheck c7r638targets c7r638 c7r638choice = true := by decide
theorem c7r638_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r638 := by
  refine ⟨c7r638targets, c7r638choice, ?_, c7r638_checked⟩
  intro S h
  simp only [c7r638targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 19 _ (by rfl)))
def c7r639 : List GridPoint := [(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)]
def c7r639targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
def c7r639choice (b : GridPoint) : ℕ × GridPoint := (([((-1,2),(0,(1,0))),((0,0),(1,(0,0))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r639_checked : successorFastRowCheck c7r639targets c7r639 c7r639choice = true := by decide
theorem c7r639_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r639 := by
  refine ⟨c7r639targets, c7r639choice, ?_, c7r639_checked⟩
  intro S h
  simp only [c7r639targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B001_lift _ (F8B001L8_lift _ (familyLookup_sound F8B001L8 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 24 _ (by rfl)))
theorem C7R00608_closed (row : List GridPoint) (h : FamilyMember row F7B000L19) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L19, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r608_closed
  · subst row; exact c7r609_closed
  · subst row; exact c7r610_closed
  · subst row; exact c7r611_closed
  · subst row; exact c7r612_closed
  · subst row; exact c7r613_closed
  · subst row; exact c7r614_closed
  · subst row; exact c7r615_closed
  · subst row; exact c7r616_closed
  · subst row; exact c7r617_closed
  · subst row; exact c7r618_closed
  · subst row; exact c7r619_closed
  · subst row; exact c7r620_closed
  · subst row; exact c7r621_closed
  · subst row; exact c7r622_closed
  · subst row; exact c7r623_closed
  · subst row; exact c7r624_closed
  · subst row; exact c7r625_closed
  · subst row; exact c7r626_closed
  · subst row; exact c7r627_closed
  · subst row; exact c7r628_closed
  · subst row; exact c7r629_closed
  · subst row; exact c7r630_closed
  · subst row; exact c7r631_closed
  · subst row; exact c7r632_closed
  · subst row; exact c7r633_closed
  · subst row; exact c7r634_closed
  · subst row; exact c7r635_closed
  · subst row; exact c7r636_closed
  · subst row; exact c7r637_closed
  · subst row; exact c7r638_closed
  · subst row; exact c7r639_closed
end Polyomino57
