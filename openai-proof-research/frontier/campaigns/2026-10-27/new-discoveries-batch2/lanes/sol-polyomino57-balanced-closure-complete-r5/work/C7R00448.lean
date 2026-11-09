import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r448 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]
def c7r448targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
def c7r448choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r448_checked : successorFastRowCheck c7r448targets c7r448 c7r448choice = true := by decide
theorem c7r448_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r448 := by
  refine ⟨c7r448targets, c7r448choice, ?_, c7r448_checked⟩
  intro S h
  simp only [c7r448targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 30 _ (by rfl)))
def c7r449 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)]
def c7r449targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
def c7r449choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r449_checked : successorFastRowCheck c7r449targets c7r449 c7r449choice = true := by decide
theorem c7r449_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r449 := by
  refine ⟨c7r449targets, c7r449choice, ?_, c7r449_checked⟩
  intro S h
  simp only [c7r449targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 1 _ (by rfl)))
def c7r450 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]
def c7r450targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
def c7r450choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r450_checked : successorFastRowCheck c7r450targets c7r450 c7r450choice = true := by decide
theorem c7r450_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r450 := by
  refine ⟨c7r450targets, c7r450choice, ?_, c7r450_checked⟩
  intro S h
  simp only [c7r450targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 4 _ (by rfl)))
def c7r451 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)]
def c7r451targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
def c7r451choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r451_checked : successorFastRowCheck c7r451targets c7r451 c7r451choice = true := by decide
theorem c7r451_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r451 := by
  refine ⟨c7r451targets, c7r451choice, ?_, c7r451_checked⟩
  intro S h
  simp only [c7r451targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 7 _ (by rfl)))
def c7r452 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]
def c7r452targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
def c7r452choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r452_checked : successorFastRowCheck c7r452targets c7r452 c7r452choice = true := by decide
theorem c7r452_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r452 := by
  refine ⟨c7r452targets, c7r452choice, ?_, c7r452_checked⟩
  intro S h
  simp only [c7r452targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 10 _ (by rfl)))
def c7r453 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
def c7r453targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r453choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r453_checked : successorFastRowCheck c7r453targets c7r453 c7r453choice = true := by decide
theorem c7r453_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r453 := by
  refine ⟨c7r453targets, c7r453choice, ?_, c7r453_checked⟩
  intro S h
  simp only [c7r453targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 15 _ (by rfl)))
def c7r454 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)]
def c7r454targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
def c7r454choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,0),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r454_checked : successorFastRowCheck c7r454targets c7r454 c7r454choice = true := by decide
theorem c7r454_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r454 := by
  refine ⟨c7r454targets, c7r454choice, ?_, c7r454_checked⟩
  intro S h
  simp only [c7r454targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 17 _ (by rfl)))
def c7r455 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]
def c7r455targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
def c7r455choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r455_checked : successorFastRowCheck c7r455targets c7r455 c7r455choice = true := by decide
theorem c7r455_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r455 := by
  refine ⟨c7r455targets, c7r455choice, ?_, c7r455_checked⟩
  intro S h
  simp only [c7r455targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 19 _ (by rfl)))
def c7r456 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)]
def c7r456targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)]]
def c7r456choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r456_checked : successorFastRowCheck c7r456targets c7r456 c7r456choice = true := by decide
theorem c7r456_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r456 := by
  refine ⟨c7r456targets, c7r456choice, ?_, c7r456_checked⟩
  intro S h
  simp only [c7r456targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 23 _ (by rfl)))
def c7r457 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)]
def c7r457targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)]]
def c7r457choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r457_checked : successorFastRowCheck c7r457targets c7r457 c7r457choice = true := by decide
theorem c7r457_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r457 := by
  refine ⟨c7r457targets, c7r457choice, ?_, c7r457_checked⟩
  intro S h
  simp only [c7r457targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 26 _ (by rfl)))
def c7r458 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]
def c7r458targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)]]
def c7r458choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r458_checked : successorFastRowCheck c7r458targets c7r458 c7r458choice = true := by decide
theorem c7r458_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r458 := by
  refine ⟨c7r458targets, c7r458choice, ?_, c7r458_checked⟩
  intro S h
  simp only [c7r458targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 29 _ (by rfl)))
def c7r459 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)]
def c7r459targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)]]
def c7r459choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r459_checked : successorFastRowCheck c7r459targets c7r459 c7r459choice = true := by decide
theorem c7r459_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r459 := by
  refine ⟨c7r459targets, c7r459choice, ?_, c7r459_checked⟩
  intro S h
  simp only [c7r459targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 0 _ (by rfl)))
def c7r460 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]
def c7r460targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)]]
def c7r460choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r460_checked : successorFastRowCheck c7r460targets c7r460 c7r460choice = true := by decide
theorem c7r460_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r460 := by
  refine ⟨c7r460targets, c7r460choice, ?_, c7r460_checked⟩
  intro S h
  simp only [c7r460targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 2 _ (by rfl)))
def c7r461 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)]
def c7r461targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)]]
def c7r461choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,4),(6,(0,0))),((3,1),(7,(0,0))),((3,2),(8,(0,0))),((3,3),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r461_checked : successorFastRowCheck c7r461targets c7r461 c7r461choice = true := by decide
theorem c7r461_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r461 := by
  refine ⟨c7r461targets, c7r461choice, ?_, c7r461_checked⟩
  intro S h
  simp only [c7r461targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 6 _ (by rfl)))
def c7r462 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)]
def c7r462targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]
def c7r462choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r462_checked : successorFastRowCheck c7r462targets c7r462 c7r462choice = true := by decide
theorem c7r462_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r462 := by
  refine ⟨c7r462targets, c7r462choice, ?_, c7r462_checked⟩
  intro S h
  simp only [c7r462targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 9 _ (by rfl)))
def c7r463 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]
def c7r463targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]
def c7r463choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,3),(6,(0,0))),((3,1),(7,(0,0))),((3,3),(8,(0,0))),((4,2),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r463_checked : successorFastRowCheck c7r463targets c7r463 c7r463choice = true := by decide
theorem c7r463_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r463 := by
  refine ⟨c7r463targets, c7r463choice, ?_, c7r463_checked⟩
  intro S h
  simp only [c7r463targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 11 _ (by rfl)))
def c7r464 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)]
def c7r464targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
def c7r464choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r464_checked : successorFastRowCheck c7r464targets c7r464 c7r464choice = true := by decide
theorem c7r464_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r464 := by
  refine ⟨c7r464targets, c7r464choice, ?_, c7r464_checked⟩
  intro S h
  simp only [c7r464targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 14 _ (by rfl)))
def c7r465 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)]
def c7r465targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]
def c7r465choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r465_checked : successorFastRowCheck c7r465targets c7r465 c7r465choice = true := by decide
theorem c7r465_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r465 := by
  refine ⟨c7r465targets, c7r465choice, ?_, c7r465_checked⟩
  intro S h
  simp only [c7r465targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L39_lift _ (familyLookup_sound F8B000L39 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 17 _ (by rfl)))
def c7r466 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]
def c7r466targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)]]
def c7r466choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r466_checked : successorFastRowCheck c7r466targets c7r466 c7r466choice = true := by decide
theorem c7r466_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r466 := by
  refine ⟨c7r466targets, c7r466choice, ?_, c7r466_checked⟩
  intro S h
  simp only [c7r466targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 20 _ (by rfl)))
def c7r467 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)]
def c7r467targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)]]
def c7r467choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((1,4),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r467_checked : successorFastRowCheck c7r467targets c7r467 c7r467choice = true := by decide
theorem c7r467_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r467 := by
  refine ⟨c7r467targets, c7r467choice, ?_, c7r467_checked⟩
  intro S h
  simp only [c7r467targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 24 _ (by rfl)))
def c7r468 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)]
def c7r468targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]
def c7r468choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r468_checked : successorFastRowCheck c7r468targets c7r468 c7r468choice = true := by decide
theorem c7r468_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r468 := by
  refine ⟨c7r468targets, c7r468choice, ?_, c7r468_checked⟩
  intro S h
  simp only [c7r468targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 27 _ (by rfl)))
def c7r469 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]
def c7r469targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)]]
def c7r469choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,2),(8,(0,0))),((3,4),(9,(0,0))),((4,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r469_checked : successorFastRowCheck c7r469targets c7r469 c7r469choice = true := by decide
theorem c7r469_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r469 := by
  refine ⟨c7r469targets, c7r469choice, ?_, c7r469_checked⟩
  intro S h
  simp only [c7r469targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 29 _ (by rfl)))
def c7r470 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)]
def c7r470targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]
def c7r470choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r470_checked : successorFastRowCheck c7r470targets c7r470 c7r470choice = true := by decide
theorem c7r470_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r470 := by
  refine ⟨c7r470targets, c7r470choice, ?_, c7r470_checked⟩
  intro S h
  simp only [c7r470targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 1 _ (by rfl)))
def c7r471 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)]
def c7r471targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)]]
def c7r471choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r471_checked : successorFastRowCheck c7r471targets c7r471 c7r471choice = true := by decide
theorem c7r471_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r471 := by
  refine ⟨c7r471targets, c7r471choice, ?_, c7r471_checked⟩
  intro S h
  simp only [c7r471targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 4 _ (by rfl)))
def c7r472 : List GridPoint := [(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]
def c7r472targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)]]
def c7r472choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,3),(4,(0,0))),((2,0),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r472_checked : successorFastRowCheck c7r472targets c7r472 c7r472choice = true := by decide
theorem c7r472_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r472 := by
  refine ⟨c7r472targets, c7r472choice, ?_, c7r472_checked⟩
  intro S h
  simp only [c7r472targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 7 _ (by rfl)))
def c7r473 : List GridPoint := [(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)]
def c7r473targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
def c7r473choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r473_checked : successorFastRowCheck c7r473targets c7r473 c7r473choice = true := by decide
theorem c7r473_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r473 := by
  refine ⟨c7r473targets, c7r473choice, ?_, c7r473_checked⟩
  intro S h
  simp only [c7r473targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L1_lift _ (familyLookup_sound F8B001L1 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 13 _ (by rfl)))
def c7r474 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)]
def c7r474targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r474choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r474_checked : successorFastRowCheck c7r474targets c7r474 c7r474choice = true := by decide
theorem c7r474_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r474 := by
  refine ⟨c7r474targets, c7r474choice, ?_, c7r474_checked⟩
  intro S h
  simp only [c7r474targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 19 _ (by rfl)))
def c7r475 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)]
def c7r475targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r475choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r475_checked : successorFastRowCheck c7r475targets c7r475 c7r475choice = true := by decide
theorem c7r475_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r475 := by
  refine ⟨c7r475targets, c7r475choice, ?_, c7r475_checked⟩
  intro S h
  simp only [c7r475targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 22 _ (by rfl)))
def c7r476 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)]
def c7r476targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r476choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r476_checked : successorFastRowCheck c7r476targets c7r476 c7r476choice = true := by decide
theorem c7r476_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r476 := by
  refine ⟨c7r476targets, c7r476choice, ?_, c7r476_checked⟩
  intro S h
  simp only [c7r476targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 24 _ (by rfl)))
def c7r477 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)]
def c7r477targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r477choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r477_checked : successorFastRowCheck c7r477targets c7r477 c7r477choice = true := by decide
theorem c7r477_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r477 := by
  refine ⟨c7r477targets, c7r477choice, ?_, c7r477_checked⟩
  intro S h
  simp only [c7r477targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 26 _ (by rfl)))
def c7r478 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)]
def c7r478targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]]
def c7r478choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r478_checked : successorFastRowCheck c7r478targets c7r478 c7r478choice = true := by decide
theorem c7r478_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r478 := by
  refine ⟨c7r478targets, c7r478choice, ?_, c7r478_checked⟩
  intro S h
  simp only [c7r478targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 29 _ (by rfl)))
def c7r479 : List GridPoint := [(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)]
def c7r479targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]]
def c7r479choice (b : GridPoint) : ℕ × GridPoint := (([((-1,1),(0,(1,0))),((0,0),(1,(0,0))),((0,2),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r479_checked : successorFastRowCheck c7r479targets c7r479 c7r479choice = true := by decide
theorem c7r479_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r479 := by
  refine ⟨c7r479targets, c7r479choice, ?_, c7r479_checked⟩
  intro S h
  simp only [c7r479targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L40_lift _ (familyLookup_sound F8B000L40 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L2_lift _ (familyLookup_sound F8B001L2 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L5_lift _ (familyLookup_sound F8B001L5 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L49_lift _ (familyLookup_sound F8B000L49 [] 31 _ (by rfl)))
theorem C7R00448_closed (row : List GridPoint) (h : FamilyMember row F7B000L14) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L14, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r448_closed
  · subst row; exact c7r449_closed
  · subst row; exact c7r450_closed
  · subst row; exact c7r451_closed
  · subst row; exact c7r452_closed
  · subst row; exact c7r453_closed
  · subst row; exact c7r454_closed
  · subst row; exact c7r455_closed
  · subst row; exact c7r456_closed
  · subst row; exact c7r457_closed
  · subst row; exact c7r458_closed
  · subst row; exact c7r459_closed
  · subst row; exact c7r460_closed
  · subst row; exact c7r461_closed
  · subst row; exact c7r462_closed
  · subst row; exact c7r463_closed
  · subst row; exact c7r464_closed
  · subst row; exact c7r465_closed
  · subst row; exact c7r466_closed
  · subst row; exact c7r467_closed
  · subst row; exact c7r468_closed
  · subst row; exact c7r469_closed
  · subst row; exact c7r470_closed
  · subst row; exact c7r471_closed
  · subst row; exact c7r472_closed
  · subst row; exact c7r473_closed
  · subst row; exact c7r474_closed
  · subst row; exact c7r475_closed
  · subst row; exact c7r476_closed
  · subst row; exact c7r477_closed
  · subst row; exact c7r478_closed
  · subst row; exact c7r479_closed
end Polyomino57
