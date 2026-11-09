import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r256 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)]
def c7r256targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
def c7r256choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,5),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r256_checked : successorFastRowCheck c7r256targets c7r256 c7r256choice = true := by decide
theorem c7r256_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r256 := by
  refine ⟨c7r256targets, c7r256choice, ?_, c7r256_checked⟩
  intro S h
  simp only [c7r256targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 13 _ (by rfl)))
def c7r257 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]
def c7r257targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
def c7r257choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r257_checked : successorFastRowCheck c7r257targets c7r257 c7r257choice = true := by decide
theorem c7r257_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r257 := by
  refine ⟨c7r257targets, c7r257choice, ?_, c7r257_checked⟩
  intro S h
  simp only [c7r257targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 16 _ (by rfl)))
def c7r258 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
def c7r258targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r258choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r258_checked : successorFastRowCheck c7r258targets c7r258 c7r258choice = true := by decide
theorem c7r258_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r258 := by
  refine ⟨c7r258targets, c7r258choice, ?_, c7r258_checked⟩
  intro S h
  simp only [c7r258targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 21 _ (by rfl)))
def c7r259 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)]
def c7r259targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
def c7r259choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r259_checked : successorFastRowCheck c7r259targets c7r259 c7r259choice = true := by decide
theorem c7r259_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r259 := by
  refine ⟨c7r259targets, c7r259choice, ?_, c7r259_checked⟩
  intro S h
  simp only [c7r259targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 23 _ (by rfl)))
def c7r260 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]
def c7r260targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
def c7r260choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r260_checked : successorFastRowCheck c7r260targets c7r260 c7r260choice = true := by decide
theorem c7r260_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r260 := by
  refine ⟨c7r260targets, c7r260choice, ?_, c7r260_checked⟩
  intro S h
  simp only [c7r260targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 25 _ (by rfl)))
def c7r261 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)]
def c7r261targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)]]
def c7r261choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r261_checked : successorFastRowCheck c7r261targets c7r261 c7r261choice = true := by decide
theorem c7r261_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r261 := by
  refine ⟨c7r261targets, c7r261choice, ?_, c7r261_checked⟩
  intro S h
  simp only [c7r261targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 29 _ (by rfl)))
def c7r262 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)]
def c7r262targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)]]
def c7r262choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r262_checked : successorFastRowCheck c7r262targets c7r262 c7r262choice = true := by decide
theorem c7r262_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r262 := by
  refine ⟨c7r262targets, c7r262choice, ?_, c7r262_checked⟩
  intro S h
  simp only [c7r262targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 0 _ (by rfl)))
def c7r263 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]
def c7r263targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)]]
def c7r263choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r263_checked : successorFastRowCheck c7r263targets c7r263 c7r263choice = true := by decide
theorem c7r263_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r263 := by
  refine ⟨c7r263targets, c7r263choice, ?_, c7r263_checked⟩
  intro S h
  simp only [c7r263targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 3 _ (by rfl)))
def c7r264 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)]
def c7r264targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)]]
def c7r264choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,2),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r264_checked : successorFastRowCheck c7r264targets c7r264 c7r264choice = true := by decide
theorem c7r264_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r264 := by
  refine ⟨c7r264targets, c7r264choice, ?_, c7r264_checked⟩
  intro S h
  simp only [c7r264targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 6 _ (by rfl)))
def c7r265 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]
def c7r265targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)]]
def c7r265choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((3,-1),(9,(0,1))),((3,1),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r265_checked : successorFastRowCheck c7r265targets c7r265 c7r265choice = true := by decide
theorem c7r265_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r265 := by
  refine ⟨c7r265targets, c7r265choice, ?_, c7r265_checked⟩
  intro S h
  simp only [c7r265targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 8 _ (by rfl)))
def c7r266 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)]
def c7r266targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)]]
def c7r266choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r266_checked : successorFastRowCheck c7r266targets c7r266 c7r266choice = true := by decide
theorem c7r266_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r266 := by
  refine ⟨c7r266targets, c7r266choice, ?_, c7r266_checked⟩
  intro S h
  simp only [c7r266targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 12 _ (by rfl)))
def c7r267 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)]
def c7r267targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]
def c7r267choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r267_checked : successorFastRowCheck c7r267targets c7r267 c7r267choice = true := by decide
theorem c7r267_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r267 := by
  refine ⟨c7r267targets, c7r267choice, ?_, c7r267_checked⟩
  intro S h
  simp only [c7r267targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 15 _ (by rfl)))
def c7r268 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]
def c7r268targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]
def c7r268choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r268_checked : successorFastRowCheck c7r268targets c7r268 c7r268choice = true := by decide
theorem c7r268_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r268 := by
  refine ⟨c7r268targets, c7r268choice, ?_, c7r268_checked⟩
  intro S h
  simp only [c7r268targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 17 _ (by rfl)))
def c7r269 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)]
def c7r269targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
def c7r269choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r269_checked : successorFastRowCheck c7r269targets c7r269 c7r269choice = true := by decide
theorem c7r269_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r269 := by
  refine ⟨c7r269targets, c7r269choice, ?_, c7r269_checked⟩
  intro S h
  simp only [c7r269targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 20 _ (by rfl)))
def c7r270 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)]
def c7r270targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]
def c7r270choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r270_checked : successorFastRowCheck c7r270targets c7r270 c7r270choice = true := by decide
theorem c7r270_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r270 := by
  refine ⟨c7r270targets, c7r270choice, ?_, c7r270_checked⟩
  intro S h
  simp only [c7r270targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 23 _ (by rfl)))
def c7r271 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]
def c7r271targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)]]
def c7r271choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r271_checked : successorFastRowCheck c7r271targets c7r271 c7r271choice = true := by decide
theorem c7r271_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r271 := by
  refine ⟨c7r271targets, c7r271choice, ?_, c7r271_checked⟩
  intro S h
  simp only [c7r271targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 26 _ (by rfl)))
def c7r272 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)]
def c7r272targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)]]
def c7r272choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,5),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r272_checked : successorFastRowCheck c7r272targets c7r272 c7r272choice = true := by decide
theorem c7r272_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r272 := by
  refine ⟨c7r272targets, c7r272choice, ?_, c7r272_checked⟩
  intro S h
  simp only [c7r272targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 30 _ (by rfl)))
def c7r273 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)]
def c7r273targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]
def c7r273choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r273_checked : successorFastRowCheck c7r273targets c7r273 c7r273choice = true := by decide
theorem c7r273_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r273 := by
  refine ⟨c7r273targets, c7r273choice, ?_, c7r273_checked⟩
  intro S h
  simp only [c7r273targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 1 _ (by rfl)))
def c7r274 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]
def c7r274targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)]]
def c7r274choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,4),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r274_checked : successorFastRowCheck c7r274targets c7r274 c7r274choice = true := by decide
theorem c7r274_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r274 := by
  refine ⟨c7r274targets, c7r274choice, ?_, c7r274_checked⟩
  intro S h
  simp only [c7r274targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 3 _ (by rfl)))
def c7r275 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)]
def c7r275targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]
def c7r275choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r275_checked : successorFastRowCheck c7r275targets c7r275 c7r275choice = true := by decide
theorem c7r275_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r275 := by
  refine ⟨c7r275targets, c7r275choice, ?_, c7r275_checked⟩
  intro S h
  simp only [c7r275targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 7 _ (by rfl)))
def c7r276 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)]
def c7r276targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)]]
def c7r276choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r276_checked : successorFastRowCheck c7r276targets c7r276 c7r276choice = true := by decide
theorem c7r276_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r276 := by
  refine ⟨c7r276targets, c7r276choice, ?_, c7r276_checked⟩
  intro S h
  simp only [c7r276targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 10 _ (by rfl)))
def c7r277 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]
def c7r277targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)]]
def c7r277choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r277_checked : successorFastRowCheck c7r277targets c7r277 c7r277choice = true := by decide
theorem c7r277_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r277 := by
  refine ⟨c7r277targets, c7r277choice, ?_, c7r277_checked⟩
  intro S h
  simp only [c7r277targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 13 _ (by rfl)))
def c7r278 : List GridPoint := [(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)]
def c7r278targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
def c7r278choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,3),(3,(0,0))),((1,-1),(4,(0,1))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r278_checked : successorFastRowCheck c7r278targets c7r278 c7r278choice = true := by decide
theorem c7r278_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r278 := by
  refine ⟨c7r278targets, c7r278choice, ?_, c7r278_checked⟩
  intro S h
  simp only [c7r278targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L47_lift _ (familyLookup_sound F8B000L47 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 19 _ (by rfl)))
def c7r279 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)]
def c7r279targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r279choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,4),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r279_checked : successorFastRowCheck c7r279targets c7r279 c7r279choice = true := by decide
theorem c7r279_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r279 := by
  refine ⟨c7r279targets, c7r279choice, ?_, c7r279_checked⟩
  intro S h
  simp only [c7r279targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 25 _ (by rfl)))
def c7r280 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)]
def c7r280targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r280choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r280_checked : successorFastRowCheck c7r280targets c7r280 c7r280choice = true := by decide
theorem c7r280_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r280 := by
  refine ⟨c7r280targets, c7r280choice, ?_, c7r280_checked⟩
  intro S h
  simp only [c7r280targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 28 _ (by rfl)))
def c7r281 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)]
def c7r281targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r281choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,1),(9,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r281_checked : successorFastRowCheck c7r281targets c7r281 c7r281choice = true := by decide
theorem c7r281_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r281 := by
  refine ⟨c7r281targets, c7r281choice, ?_, c7r281_checked⟩
  intro S h
  simp only [c7r281targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 30 _ (by rfl)))
def c7r282 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)]
def c7r282targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r282choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,3),(6,(0,0))),((3,0),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r282_checked : successorFastRowCheck c7r282targets c7r282 c7r282choice = true := by decide
theorem c7r282_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r282 := by
  refine ⟨c7r282targets, c7r282choice, ?_, c7r282_checked⟩
  intro S h
  simp only [c7r282targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 0 _ (by rfl)))
def c7r283 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)]
def c7r283targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]]
def c7r283choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r283_checked : successorFastRowCheck c7r283targets c7r283 c7r283choice = true := by decide
theorem c7r283_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r283 := by
  refine ⟨c7r283targets, c7r283choice, ?_, c7r283_checked⟩
  intro S h
  simp only [c7r283targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 3 _ (by rfl)))
def c7r284 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)]
def c7r284targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]]
def c7r284choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r284_checked : successorFastRowCheck c7r284targets c7r284 c7r284choice = true := by decide
theorem c7r284_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r284 := by
  refine ⟨c7r284targets, c7r284choice, ?_, c7r284_checked⟩
  intro S h
  simp only [c7r284targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 5 _ (by rfl)))
def c7r285 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)]
def c7r285targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]
def c7r285choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r285_checked : successorFastRowCheck c7r285targets c7r285 c7r285choice = true := by decide
theorem c7r285_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r285 := by
  refine ⟨c7r285targets, c7r285choice, ?_, c7r285_checked⟩
  intro S h
  simp only [c7r285targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 8 _ (by rfl)))
def c7r286 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)]
def c7r286targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]]
def c7r286choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r286_checked : successorFastRowCheck c7r286targets c7r286 c7r286choice = true := by decide
theorem c7r286_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r286 := by
  refine ⟨c7r286targets, c7r286choice, ?_, c7r286_checked⟩
  intro S h
  simp only [c7r286targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 11 _ (by rfl)))
def c7r287 : List GridPoint := [(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)]
def c7r287targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)]]
def c7r287choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,2),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r287_checked : successorFastRowCheck c7r287targets c7r287 c7r287choice = true := by decide
theorem c7r287_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r287 := by
  refine ⟨c7r287targets, c7r287choice, ?_, c7r287_checked⟩
  intro S h
  simp only [c7r287targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L48_lift _ (familyLookup_sound F8B000L48 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L27_lift _ (familyLookup_sound F8B000L27 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L53_lift _ (familyLookup_sound F8B000L53 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L54_lift _ (familyLookup_sound F8B000L54 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 16 _ (by rfl)))
theorem C7R00256_closed (row : List GridPoint) (h : FamilyMember row F7B000L8) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L8, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r256_closed
  · subst row; exact c7r257_closed
  · subst row; exact c7r258_closed
  · subst row; exact c7r259_closed
  · subst row; exact c7r260_closed
  · subst row; exact c7r261_closed
  · subst row; exact c7r262_closed
  · subst row; exact c7r263_closed
  · subst row; exact c7r264_closed
  · subst row; exact c7r265_closed
  · subst row; exact c7r266_closed
  · subst row; exact c7r267_closed
  · subst row; exact c7r268_closed
  · subst row; exact c7r269_closed
  · subst row; exact c7r270_closed
  · subst row; exact c7r271_closed
  · subst row; exact c7r272_closed
  · subst row; exact c7r273_closed
  · subst row; exact c7r274_closed
  · subst row; exact c7r275_closed
  · subst row; exact c7r276_closed
  · subst row; exact c7r277_closed
  · subst row; exact c7r278_closed
  · subst row; exact c7r279_closed
  · subst row; exact c7r280_closed
  · subst row; exact c7r281_closed
  · subst row; exact c7r282_closed
  · subst row; exact c7r283_closed
  · subst row; exact c7r284_closed
  · subst row; exact c7r285_closed
  · subst row; exact c7r286_closed
  · subst row; exact c7r287_closed
end Polyomino57
