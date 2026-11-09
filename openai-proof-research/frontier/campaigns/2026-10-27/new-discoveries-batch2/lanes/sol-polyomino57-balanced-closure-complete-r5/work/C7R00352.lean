import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r352 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)]
def c7r352targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)]]
def c7r352choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,-1),(13,(0,1))),((6,1),(14,(0,0))),((7,0),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r352_checked : successorFastRowCheck c7r352targets c7r352 c7r352choice = true := by decide
theorem c7r352_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r352 := by
  refine ⟨c7r352targets, c7r352choice, ?_, c7r352_checked⟩
  intro S h
  simp only [c7r352targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 25 _ (by rfl)))
def c7r353 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1)]
def c7r353targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)]]
def c7r353choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,0),(5,(0,0))),((0,6),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r353_checked : successorFastRowCheck c7r353targets c7r353 c7r353choice = true := by decide
theorem c7r353_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r353 := by
  refine ⟨c7r353targets, c7r353choice, ?_, c7r353_checked⟩
  intro S h
  simp only [c7r353targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 0 _ (by rfl)))
def c7r354 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)]
def c7r354targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)]]
def c7r354choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r354_checked : successorFastRowCheck c7r354targets c7r354 c7r354choice = true := by decide
theorem c7r354_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r354 := by
  refine ⟨c7r354targets, c7r354choice, ?_, c7r354_checked⟩
  intro S h
  simp only [c7r354targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 6 _ (by rfl)))
def c7r355 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3)]
def c7r355targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)]]
def c7r355choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r355_checked : successorFastRowCheck c7r355targets c7r355 c7r355choice = true := by decide
theorem c7r355_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r355 := by
  refine ⟨c7r355targets, c7r355choice, ?_, c7r355_checked⟩
  intro S h
  simp only [c7r355targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 10 _ (by rfl)))
def c7r356 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4)]
def c7r356targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,4)]]
def c7r356choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r356_checked : successorFastRowCheck c7r356targets c7r356 c7r356choice = true := by decide
theorem c7r356_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r356 := by
  refine ⟨c7r356targets, c7r356choice, ?_, c7r356_checked⟩
  intro S h
  simp only [c7r356targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 14 _ (by rfl)))
def c7r357 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0)]
def c7r357targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,0)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0)]]
def c7r357choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r357_checked : successorFastRowCheck c7r357targets c7r357 c7r357choice = true := by decide
theorem c7r357_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r357 := by
  refine ⟨c7r357targets, c7r357choice, ?_, c7r357_checked⟩
  intro S h
  simp only [c7r357targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 16 _ (by rfl)))
def c7r358 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1)]
def c7r358targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)]]
def c7r358choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r358_checked : successorFastRowCheck c7r358targets c7r358 c7r358choice = true := by decide
theorem c7r358_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r358 := by
  refine ⟨c7r358targets, c7r358choice, ?_, c7r358_checked⟩
  intro S h
  simp only [c7r358targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 18 _ (by rfl)))
def c7r359 : List GridPoint := [(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1)]
def c7r359targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)]]
def c7r359choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,0),(4,(0,0))),((0,5),(5,(0,0))),((1,0),(6,(0,0))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,2),(11,(0,0))),((3,0),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r359_checked : successorFastRowCheck c7r359targets c7r359 c7r359choice = true := by decide
theorem c7r359_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r359 := by
  refine ⟨c7r359targets, c7r359choice, ?_, c7r359_checked⟩
  intro S h
  simp only [c7r359targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 24 _ (by rfl)))
def c7r360 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)]
def c7r360targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]]
def c7r360choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r360_checked : successorFastRowCheck c7r360targets c7r360 c7r360choice = true := by decide
theorem c7r360_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r360 := by
  refine ⟨c7r360targets, c7r360choice, ?_, c7r360_checked⟩
  intro S h
  simp only [c7r360targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 31 _ (by rfl)))
def c7r361 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)]
def c7r361targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)]]
def c7r361choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((3,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r361_checked : successorFastRowCheck c7r361targets c7r361 c7r361choice = true := by decide
theorem c7r361_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r361 := by
  refine ⟨c7r361targets, c7r361choice, ?_, c7r361_checked⟩
  intro S h
  simp only [c7r361targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 2 _ (by rfl)))
def c7r362 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)]
def c7r362targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)]]
def c7r362choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r362_checked : successorFastRowCheck c7r362targets c7r362 c7r362choice = true := by decide
theorem c7r362_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r362 := by
  refine ⟨c7r362targets, c7r362choice, ?_, c7r362_checked⟩
  intro S h
  simp only [c7r362targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 4 _ (by rfl)))
def c7r363 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)]
def c7r363targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)]]
def c7r363choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r363_checked : successorFastRowCheck c7r363targets c7r363 c7r363choice = true := by decide
theorem c7r363_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r363 := by
  refine ⟨c7r363targets, c7r363choice, ?_, c7r363_checked⟩
  intro S h
  simp only [c7r363targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 6 _ (by rfl)))
def c7r364 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4)]
def c7r364targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(1,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,4)]]
def c7r364choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r364_checked : successorFastRowCheck c7r364targets c7r364 c7r364choice = true := by decide
theorem c7r364_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r364 := by
  refine ⟨c7r364targets, c7r364choice, ?_, c7r364_checked⟩
  intro S h
  simp only [c7r364targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 11 _ (by rfl)))
def c7r365 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0)]
def c7r365targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0)]]
def c7r365choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r365_checked : successorFastRowCheck c7r365targets c7r365 c7r365choice = true := by decide
theorem c7r365_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r365 := by
  refine ⟨c7r365targets, c7r365choice, ?_, c7r365_checked⟩
  intro S h
  simp only [c7r365targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 14 _ (by rfl)))
def c7r366 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1)]
def c7r366targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)]]
def c7r366choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r366_checked : successorFastRowCheck c7r366targets c7r366 c7r366choice = true := by decide
theorem c7r366_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r366 := by
  refine ⟨c7r366targets, c7r366choice, ?_, c7r366_checked⟩
  intro S h
  simp only [c7r366targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 17 _ (by rfl)))
def c7r367 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3)]
def c7r367targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3),(3,3)]]
def c7r367choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r367_checked : successorFastRowCheck c7r367targets c7r367 c7r367choice = true := by decide
theorem c7r367_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r367 := by
  refine ⟨c7r367targets, c7r367choice, ?_, c7r367_checked⟩
  intro S h
  simp only [c7r367targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 20 _ (by rfl)))
def c7r368 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)]
def c7r368targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)]]
def c7r368choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r368_checked : successorFastRowCheck c7r368targets c7r368 c7r368choice = true := by decide
theorem c7r368_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r368 := by
  refine ⟨c7r368targets, c7r368choice, ?_, c7r368_checked⟩
  intro S h
  simp only [c7r368targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 23 _ (by rfl)))
def c7r369 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0)]
def c7r369targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0),(4,0)]]
def c7r369choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r369_checked : successorFastRowCheck c7r369targets c7r369 c7r369choice = true := by decide
theorem c7r369_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r369 := by
  refine ⟨c7r369targets, c7r369choice, ?_, c7r369_checked⟩
  intro S h
  simp only [c7r369targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 25 _ (by rfl)))
def c7r370 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2)]
def c7r370targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,2)]]
def c7r370choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r370_checked : successorFastRowCheck c7r370targets c7r370 c7r370choice = true := by decide
theorem c7r370_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r370 := by
  refine ⟨c7r370targets, c7r370choice, ?_, c7r370_checked⟩
  intro S h
  simp only [c7r370targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 28 _ (by rfl)))
def c7r371 : List GridPoint := [(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1)]
def c7r371targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1)]]
def c7r371choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r371_checked : successorFastRowCheck c7r371targets c7r371 c7r371choice = true := by decide
theorem c7r371_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r371 := by
  refine ⟨c7r371targets, c7r371choice, ?_, c7r371_checked⟩
  intro S h
  simp only [c7r371targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L59_lift _ (familyLookup_sound F8B000L59 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 31 _ (by rfl)))
def c7r372 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)]
def c7r372targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)]]
def c7r372choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r372_checked : successorFastRowCheck c7r372targets c7r372 c7r372choice = true := by decide
theorem c7r372_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r372 := by
  refine ⟨c7r372targets, c7r372choice, ?_, c7r372_checked⟩
  intro S h
  simp only [c7r372targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 4 _ (by rfl)))
def c7r373 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1)]
def c7r373targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)]]
def c7r373choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r373_checked : successorFastRowCheck c7r373targets c7r373 c7r373choice = true := by decide
theorem c7r373_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r373 := by
  refine ⟨c7r373targets, c7r373choice, ?_, c7r373_checked⟩
  intro S h
  simp only [c7r373targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 10 _ (by rfl)))
def c7r374 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2)]
def c7r374targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,2)]]
def c7r374choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r374_checked : successorFastRowCheck c7r374targets c7r374 c7r374choice = true := by decide
theorem c7r374_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r374 := by
  refine ⟨c7r374targets, c7r374choice, ?_, c7r374_checked⟩
  intro S h
  simp only [c7r374targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 15 _ (by rfl)))
def c7r375 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0)]
def c7r375targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0)]]
def c7r375choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r375_checked : successorFastRowCheck c7r375targets c7r375 c7r375choice = true := by decide
theorem c7r375_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r375 := by
  refine ⟨c7r375targets, c7r375choice, ?_, c7r375_checked⟩
  intro S h
  simp only [c7r375targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 17 _ (by rfl)))
def c7r376 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1)]
def c7r376targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1)]]
def c7r376choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,2),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r376_checked : successorFastRowCheck c7r376targets c7r376 c7r376choice = true := by decide
theorem c7r376_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r376 := by
  refine ⟨c7r376targets, c7r376choice, ?_, c7r376_checked⟩
  intro S h
  simp only [c7r376targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 19 _ (by rfl)))
def c7r377 : List GridPoint := [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1)]
def c7r377targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1)]]
def c7r377choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,2),(11,(0,0))),((4,0),(12,(0,0))),((4,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r377_checked : successorFastRowCheck c7r377targets c7r377 c7r377choice = true := by decide
theorem c7r377_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r377 := by
  refine ⟨c7r377targets, c7r377choice, ?_, c7r377_checked⟩
  intro S h
  simp only [c7r377targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L37_lift _ (familyLookup_sound F8B000L37 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 23 _ (by rfl)))
def c7r378 : List GridPoint := [(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2)]
def c7r378targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r378choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,0),(3,(0,0))),((0,4),(4,(0,0))),((1,0),(5,(0,0))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r378_checked : successorFastRowCheck c7r378targets c7r378 c7r378choice = true := by decide
theorem c7r378_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r378 := by
  refine ⟨c7r378targets, c7r378choice, ?_, c7r378_checked⟩
  intro S h
  simp only [c7r378targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L15_lift _ (familyLookup_sound F8B001L15 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L4_lift _ (familyLookup_sound F8B000L4 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L38_lift _ (familyLookup_sound F8B000L38 [] 29 _ (by rfl)))
def c7r379 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r379targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r379choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((0,4),(4,(0,0))),((1,-1),(5,(0,1))),((1,5),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r379_checked : successorFastRowCheck c7r379targets c7r379 c7r379choice = true := by decide
theorem c7r379_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r379 := by
  refine ⟨c7r379targets, c7r379choice, ?_, c7r379_checked⟩
  intro S h
  simp only [c7r379targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 7 _ (by rfl)))
def c7r380 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)]
def c7r380targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
def c7r380choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r380_checked : successorFastRowCheck c7r380targets c7r380 c7r380choice = true := by decide
theorem c7r380_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r380 := by
  refine ⟨c7r380targets, c7r380choice, ?_, c7r380_checked⟩
  intro S h
  simp only [c7r380targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L61_lift _ (familyLookup_sound F8B000L61 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 11 _ (by rfl)))
def c7r381 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)]
def c7r381targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
def c7r381choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r381_checked : successorFastRowCheck c7r381targets c7r381 c7r381choice = true := by decide
theorem c7r381_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r381 := by
  refine ⟨c7r381targets, c7r381choice, ?_, c7r381_checked⟩
  intro S h
  simp only [c7r381targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 14 _ (by rfl)))
def c7r382 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)]
def c7r382targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
def c7r382choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,2),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r382_checked : successorFastRowCheck c7r382targets c7r382 c7r382choice = true := by decide
theorem c7r382_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r382 := by
  refine ⟨c7r382targets, c7r382choice, ?_, c7r382_checked⟩
  intro S h
  simp only [c7r382targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 16 _ (by rfl)))
def c7r383 : List GridPoint := [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)]
def c7r383targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
def c7r383choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((-1,2),(1,(1,0))),((0,0),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r383_checked : successorFastRowCheck c7r383targets c7r383 c7r383choice = true := by decide
theorem c7r383_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r383 := by
  refine ⟨c7r383targets, c7r383choice, ?_, c7r383_checked⟩
  intro S h
  simp only [c7r383targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L60_lift _ (familyLookup_sound F8B000L60 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 18 _ (by rfl)))
theorem C7R00352_closed (row : List GridPoint) (h : FamilyMember row F7B000L11) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L11, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r352_closed
  · subst row; exact c7r353_closed
  · subst row; exact c7r354_closed
  · subst row; exact c7r355_closed
  · subst row; exact c7r356_closed
  · subst row; exact c7r357_closed
  · subst row; exact c7r358_closed
  · subst row; exact c7r359_closed
  · subst row; exact c7r360_closed
  · subst row; exact c7r361_closed
  · subst row; exact c7r362_closed
  · subst row; exact c7r363_closed
  · subst row; exact c7r364_closed
  · subst row; exact c7r365_closed
  · subst row; exact c7r366_closed
  · subst row; exact c7r367_closed
  · subst row; exact c7r368_closed
  · subst row; exact c7r369_closed
  · subst row; exact c7r370_closed
  · subst row; exact c7r371_closed
  · subst row; exact c7r372_closed
  · subst row; exact c7r373_closed
  · subst row; exact c7r374_closed
  · subst row; exact c7r375_closed
  · subst row; exact c7r376_closed
  · subst row; exact c7r377_closed
  · subst row; exact c7r378_closed
  · subst row; exact c7r379_closed
  · subst row; exact c7r380_closed
  · subst row; exact c7r381_closed
  · subst row; exact c7r382_closed
  · subst row; exact c7r383_closed
end Polyomino57
