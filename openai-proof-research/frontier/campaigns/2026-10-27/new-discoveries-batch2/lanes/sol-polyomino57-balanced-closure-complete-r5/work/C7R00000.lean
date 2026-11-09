import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r0 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)]
def c7r0targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6)]]
def c7r0choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r0_checked : successorFastRowCheck c7r0targets c7r0 c7r0choice = true := by decide
theorem c7r0_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r0 := by
  refine ⟨c7r0targets, c7r0choice, ?_, c7r0_checked⟩
  intro S h
  simp only [c7r0targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L63_lift _ (familyLookup_sound F8B000L63 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L21_lift _ (familyLookup_sound F8B001L21 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 7 _ (by rfl)))
def c7r1 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0)]
def c7r1targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0)]]
def c7r1choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((2,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r1_checked : successorFastRowCheck c7r1targets c7r1 c7r1choice = true := by decide
theorem c7r1_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r1 := by
  refine ⟨c7r1targets, c7r1choice, ?_, c7r1_checked⟩
  intro S h
  simp only [c7r1targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 13 _ (by rfl)))
def c7r2 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1)]
def c7r2targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1)]]
def c7r2choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r2_checked : successorFastRowCheck c7r2targets c7r2 c7r2choice = true := by decide
theorem c7r2_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r2 := by
  refine ⟨c7r2targets, c7r2choice, ?_, c7r2_checked⟩
  intro S h
  simp only [c7r2targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 18 _ (by rfl)))
def c7r3 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2)]
def c7r3targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2)]]
def c7r3choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r3_checked : successorFastRowCheck c7r3targets c7r3 c7r3choice = true := by decide
theorem c7r3_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r3 := by
  refine ⟨c7r3targets, c7r3choice, ?_, c7r3_checked⟩
  intro S h
  simp only [c7r3targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 22 _ (by rfl)))
def c7r4 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3)]
def c7r4targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3)]]
def c7r4choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r4_checked : successorFastRowCheck c7r4targets c7r4 c7r4choice = true := by decide
theorem c7r4_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r4 := by
  refine ⟨c7r4targets, c7r4choice, ?_, c7r4_checked⟩
  intro S h
  simp only [c7r4targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 25 _ (by rfl)))
def c7r5 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4)]
def c7r5targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4)]]
def c7r5choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,5),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r5_checked : successorFastRowCheck c7r5targets c7r5 c7r5choice = true := by decide
theorem c7r5_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r5 := by
  refine ⟨c7r5targets, c7r5choice, ?_, c7r5_checked⟩
  intro S h
  simp only [c7r5targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 27 _ (by rfl)))
def c7r6 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5)]
def c7r6targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,5)]]
def c7r6choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,6),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r6_checked : successorFastRowCheck c7r6targets c7r6 c7r6choice = true := by decide
theorem c7r6_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r6 := by
  refine ⟨c7r6targets, c7r6choice, ?_, c7r6_checked⟩
  intro S h
  simp only [c7r6targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L20_lift _ (familyLookup_sound F8B001L20 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 29 _ (by rfl)))
def c7r7 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1)]
def c7r7targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1)]]
def c7r7choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r7_checked : successorFastRowCheck c7r7targets c7r7 c7r7choice = true := by decide
theorem c7r7_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r7 := by
  refine ⟨c7r7targets, c7r7choice, ?_, c7r7_checked⟩
  intro S h
  simp only [c7r7targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 2 _ (by rfl)))
def c7r8 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2)]
def c7r8targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2)]]
def c7r8choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r8_checked : successorFastRowCheck c7r8targets c7r8 c7r8choice = true := by decide
theorem c7r8_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r8 := by
  refine ⟨c7r8targets, c7r8choice, ?_, c7r8_checked⟩
  intro S h
  simp only [c7r8targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 6 _ (by rfl)))
def c7r9 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3)]
def c7r9targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3)]]
def c7r9choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r9_checked : successorFastRowCheck c7r9targets c7r9 c7r9choice = true := by decide
theorem c7r9_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r9 := by
  refine ⟨c7r9targets, c7r9choice, ?_, c7r9_checked⟩
  intro S h
  simp only [c7r9targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 9 _ (by rfl)))
def c7r10 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4)]
def c7r10targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4)]]
def c7r10choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,0),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r10_checked : successorFastRowCheck c7r10targets c7r10 c7r10choice = true := by decide
theorem c7r10_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r10 := by
  refine ⟨c7r10targets, c7r10choice, ?_, c7r10_checked⟩
  intro S h
  simp only [c7r10targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 12 _ (by rfl)))
def c7r11 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0)]
def c7r11targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(2,0),(3,0)]]
def c7r11choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((2,-1),(12,(0,1))),((2,1),(13,(0,0))),((3,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r11_checked : successorFastRowCheck c7r11targets c7r11 c7r11choice = true := by decide
theorem c7r11_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r11 := by
  refine ⟨c7r11targets, c7r11choice, ?_, c7r11_checked⟩
  intro S h
  simp only [c7r11targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L18_lift _ (familyLookup_sound F8B001L18 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 14 _ (by rfl)))
def c7r12 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2)]
def c7r12targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2)]]
def c7r12choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r12_checked : successorFastRowCheck c7r12targets c7r12 c7r12choice = true := by decide
theorem c7r12_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r12 := by
  refine ⟨c7r12targets, c7r12choice, ?_, c7r12_checked⟩
  intro S h
  simp only [c7r12targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 18 _ (by rfl)))
def c7r13 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3)]
def c7r13targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3)]]
def c7r13choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r13_checked : successorFastRowCheck c7r13targets c7r13 c7r13choice = true := by decide
theorem c7r13_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r13 := by
  refine ⟨c7r13targets, c7r13choice, ?_, c7r13_checked⟩
  intro S h
  simp only [c7r13targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 21 _ (by rfl)))
def c7r14 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4)]
def c7r14targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4)]]
def c7r14choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,1),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r14_checked : successorFastRowCheck c7r14targets c7r14 c7r14choice = true := by decide
theorem c7r14_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r14 := by
  refine ⟨c7r14targets, c7r14choice, ?_, c7r14_checked⟩
  intro S h
  simp only [c7r14targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 24 _ (by rfl)))
def c7r15 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1)]
def c7r15targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1)]]
def c7r15choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,2),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,0),(11,(0,0))),((2,2),(12,(0,0))),((3,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r15_checked : successorFastRowCheck c7r15targets c7r15 c7r15choice = true := by decide
theorem c7r15_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r15 := by
  refine ⟨c7r15targets, c7r15choice, ?_, c7r15_checked⟩
  intro S h
  simp only [c7r15targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 27 _ (by rfl)))
def c7r16 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3)]
def c7r16targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3)]]
def c7r16choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r16_checked : successorFastRowCheck c7r16targets c7r16 c7r16choice = true := by decide
theorem c7r16_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r16 := by
  refine ⟨c7r16targets, c7r16choice, ?_, c7r16_checked⟩
  intro S h
  simp only [c7r16targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 30 _ (by rfl)))
def c7r17 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4)]
def c7r17targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4)]]
def c7r17choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r17_checked : successorFastRowCheck c7r17targets c7r17 c7r17choice = true := by decide
theorem c7r17_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r17 := by
  refine ⟨c7r17targets, c7r17choice, ?_, c7r17_checked⟩
  intro S h
  simp only [c7r17targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 1 _ (by rfl)))
def c7r18 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2)]
def c7r18targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2)]]
def c7r18choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r18_checked : successorFastRowCheck c7r18targets c7r18 c7r18choice = true := by decide
theorem c7r18_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r18 := by
  refine ⟨c7r18targets, c7r18choice, ?_, c7r18_checked⟩
  intro S h
  simp only [c7r18targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 4 _ (by rfl)))
def c7r19 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4)]
def c7r19targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)]]
def c7r19choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,5),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r19_checked : successorFastRowCheck c7r19targets c7r19 c7r19choice = true := by decide
theorem c7r19_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r19 := by
  refine ⟨c7r19targets, c7r19choice, ?_, c7r19_checked⟩
  intro S h
  simp only [c7r19targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 7 _ (by rfl)))
def c7r20 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3)]
def c7r20targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3)]]
def c7r20choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r20_checked : successorFastRowCheck c7r20targets c7r20 c7r20choice = true := by decide
theorem c7r20_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r20 := by
  refine ⟨c7r20targets, c7r20choice, ?_, c7r20_checked⟩
  intro S h
  simp only [c7r20targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 10 _ (by rfl)))
def c7r21 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5)]
def c7r21targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5)]]
def c7r21choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,6),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r21_checked : successorFastRowCheck c7r21targets c7r21 c7r21choice = true := by decide
theorem c7r21_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r21 := by
  refine ⟨c7r21targets, c7r21choice, ?_, c7r21_checked⟩
  intro S h
  simp only [c7r21targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 13 _ (by rfl)))
def c7r22 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4)]
def c7r22targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4)]]
def c7r22choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,3),(12,(0,0))),((2,5),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r22_checked : successorFastRowCheck c7r22targets c7r22 c7r22choice = true := by decide
theorem c7r22_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r22 := by
  refine ⟨c7r22targets, c7r22choice, ?_, c7r22_checked⟩
  intro S h
  simp only [c7r22targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L12_lift _ (familyLookup_sound F8B001L12 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 16 _ (by rfl)))
def c7r23 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2)]
def c7r23targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)]]
def c7r23choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r23_checked : successorFastRowCheck c7r23targets c7r23 c7r23choice = true := by decide
theorem c7r23_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r23 := by
  refine ⟨c7r23targets, c7r23choice, ?_, c7r23_checked⟩
  intro S h
  simp only [c7r23targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 10 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 21 _ (by rfl)))
def c7r24 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3)]
def c7r24targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,3)]]
def c7r24choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r24_checked : successorFastRowCheck c7r24targets c7r24 c7r24choice = true := by decide
theorem c7r24_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r24 := by
  refine ⟨c7r24targets, c7r24choice, ?_, c7r24_checked⟩
  intro S h
  simp only [c7r24targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 11 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 25 _ (by rfl)))
def c7r25 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0)]
def c7r25targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(3,0)]]
def c7r25choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r25_checked : successorFastRowCheck c7r25targets c7r25 c7r25choice = true := by decide
theorem c7r25_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r25 := by
  refine ⟨c7r25targets, c7r25choice, ?_, c7r25_checked⟩
  intro S h
  simp only [c7r25targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 27 _ (by rfl)))
def c7r26 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1)]
def c7r26targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1)]]
def c7r26choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,2),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r26_checked : successorFastRowCheck c7r26targets c7r26 c7r26choice = true := by decide
theorem c7r26_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r26 := by
  refine ⟨c7r26targets, c7r26choice, ?_, c7r26_checked⟩
  intro S h
  simp only [c7r26targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 13 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 29 _ (by rfl)))
def c7r27 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3)]
def c7r27targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,3)]]
def c7r27choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r27_checked : successorFastRowCheck c7r27targets c7r27 c7r27choice = true := by decide
theorem c7r27_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r27 := by
  refine ⟨c7r27targets, c7r27choice, ?_, c7r27_checked⟩
  intro S h
  simp only [c7r27targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 14 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 1 _ (by rfl)))
def c7r28 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0)]
def c7r28targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(3,0)]]
def c7r28choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,-1),(9,(0,1))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r28_checked : successorFastRowCheck c7r28targets c7r28 c7r28choice = true := by decide
theorem c7r28_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r28 := by
  refine ⟨c7r28targets, c7r28choice, ?_, c7r28_checked⟩
  intro S h
  simp only [c7r28targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 15 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 4 _ (by rfl)))
def c7r29 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2)]
def c7r29targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2)]]
def c7r29choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r29_checked : successorFastRowCheck c7r29targets c7r29 c7r29choice = true := by decide
theorem c7r29_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r29 := by
  refine ⟨c7r29targets, c7r29choice, ?_, c7r29_checked⟩
  intro S h
  simp only [c7r29targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 16 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 7 _ (by rfl)))
def c7r30 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4)]
def c7r30targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4)]]
def c7r30choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r30_checked : successorFastRowCheck c7r30targets c7r30 c7r30choice = true := by decide
theorem c7r30_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r30 := by
  refine ⟨c7r30targets, c7r30choice, ?_, c7r30_checked⟩
  intro S h
  simp only [c7r30targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 11 _ (by rfl)))
def c7r31 : List GridPoint := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0)]
def c7r31targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,4),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(3,0)]]
def c7r31choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,-1),(10,(0,1))),((2,1),(11,(0,0))),((2,3),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r31_checked : successorFastRowCheck c7r31targets c7r31 c7r31choice = true := by decide
theorem c7r31_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r31 := by
  refine ⟨c7r31targets, c7r31choice, ?_, c7r31_checked⟩
  intro S h
  simp only [c7r31targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L0_lift _ (familyLookup_sound F8B001L0 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L13_lift _ (familyLookup_sound F8B001L13 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L1_lift _ (familyLookup_sound F8B000L1 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L36_lift _ (familyLookup_sound F8B000L36 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L3_lift _ (familyLookup_sound F8B000L3 [] 14 _ (by rfl)))
theorem C7R00000_closed (row : List GridPoint) (h : FamilyMember row F7B000L0) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L0, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r0_closed
  · subst row; exact c7r1_closed
  · subst row; exact c7r2_closed
  · subst row; exact c7r3_closed
  · subst row; exact c7r4_closed
  · subst row; exact c7r5_closed
  · subst row; exact c7r6_closed
  · subst row; exact c7r7_closed
  · subst row; exact c7r8_closed
  · subst row; exact c7r9_closed
  · subst row; exact c7r10_closed
  · subst row; exact c7r11_closed
  · subst row; exact c7r12_closed
  · subst row; exact c7r13_closed
  · subst row; exact c7r14_closed
  · subst row; exact c7r15_closed
  · subst row; exact c7r16_closed
  · subst row; exact c7r17_closed
  · subst row; exact c7r18_closed
  · subst row; exact c7r19_closed
  · subst row; exact c7r20_closed
  · subst row; exact c7r21_closed
  · subst row; exact c7r22_closed
  · subst row; exact c7r23_closed
  · subst row; exact c7r24_closed
  · subst row; exact c7r25_closed
  · subst row; exact c7r26_closed
  · subst row; exact c7r27_closed
  · subst row; exact c7r28_closed
  · subst row; exact c7r29_closed
  · subst row; exact c7r30_closed
  · subst row; exact c7r31_closed
end Polyomino57
