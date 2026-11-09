import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r224 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)]
def c7r224targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
def c7r224choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r224_checked : successorFastRowCheck c7r224targets c7r224 c7r224choice = true := by decide
theorem c7r224_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r224 := by
  refine ⟨c7r224targets, c7r224choice, ?_, c7r224_checked⟩
  intro S h
  simp only [c7r224targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 25 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 27 _ (by rfl)))
def c7r225 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)]
def c7r225targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
def c7r225choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r225_checked : successorFastRowCheck c7r225targets c7r225 c7r225choice = true := by decide
theorem c7r225_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r225 := by
  refine ⟨c7r225targets, c7r225choice, ?_, c7r225_checked⟩
  intro S h
  simp only [c7r225targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 26 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 29 _ (by rfl)))
def c7r226 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)]
def c7r226targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)]]
def c7r226choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r226_checked : successorFastRowCheck c7r226targets c7r226 c7r226choice = true := by decide
theorem c7r226_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r226 := by
  refine ⟨c7r226targets, c7r226choice, ?_, c7r226_checked⟩
  intro S h
  simp only [c7r226targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 27 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 0 _ (by rfl)))
def c7r227 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)]
def c7r227targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)]]
def c7r227choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r227_checked : successorFastRowCheck c7r227targets c7r227 c7r227choice = true := by decide
theorem c7r227_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r227 := by
  refine ⟨c7r227targets, c7r227choice, ?_, c7r227_checked⟩
  intro S h
  simp only [c7r227targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 28 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 3 _ (by rfl)))
def c7r228 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)]
def c7r228targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)]]
def c7r228choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((3,-1),(10,(0,1))),((3,1),(11,(0,0))),((4,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r228_checked : successorFastRowCheck c7r228targets c7r228 c7r228choice = true := by decide
theorem c7r228_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r228 := by
  refine ⟨c7r228targets, c7r228choice, ?_, c7r228_checked⟩
  intro S h
  simp only [c7r228targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 29 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 5 _ (by rfl)))
def c7r229 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)]
def c7r229targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)]]
def c7r229choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r229_checked : successorFastRowCheck c7r229targets c7r229 c7r229choice = true := by decide
theorem c7r229_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r229 := by
  refine ⟨c7r229targets, c7r229choice, ?_, c7r229_checked⟩
  intro S h
  simp only [c7r229targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 30 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 8 _ (by rfl)))
def c7r230 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)]
def c7r230targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)]]
def c7r230choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r230_checked : successorFastRowCheck c7r230targets c7r230 c7r230choice = true := by decide
theorem c7r230_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r230 := by
  refine ⟨c7r230targets, c7r230choice, ?_, c7r230_checked⟩
  intro S h
  simp only [c7r230targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 31 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 11 _ (by rfl)))
def c7r231 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)]
def c7r231targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)]]
def c7r231choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r231_checked : successorFastRowCheck c7r231targets c7r231 c7r231choice = true := by decide
theorem c7r231_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r231 := by
  refine ⟨c7r231targets, c7r231choice, ?_, c7r231_checked⟩
  intro S h
  simp only [c7r231targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 0 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 14 _ (by rfl)))
def c7r232 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)]
def c7r232targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)]]
def c7r232choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r232_checked : successorFastRowCheck c7r232targets c7r232 c7r232choice = true := by decide
theorem c7r232_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r232 := by
  refine ⟨c7r232targets, c7r232choice, ?_, c7r232_checked⟩
  intro S h
  simp only [c7r232targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 1 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 17 _ (by rfl)))
def c7r233 : List GridPoint := [(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)]
def c7r233targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r233choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,1),(6,(0,0))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r233_checked : successorFastRowCheck c7r233targets c7r233 c7r233choice = true := by decide
theorem c7r233_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r233 := by
  refine ⟨c7r233targets, c7r233choice, ?_, c7r233_checked⟩
  intro S h
  simp only [c7r233targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 2 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L4_lift _ (familyLookup_sound F8B001L4 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L7_lift _ (familyLookup_sound F8B000L7 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 22 _ (by rfl)))
def c7r234 : List GridPoint := [(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)]
def c7r234targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)]]
def c7r234choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((-1,4),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,2),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,4),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r234_checked : successorFastRowCheck c7r234targets c7r234 c7r234choice = true := by decide
theorem c7r234_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r234 := by
  refine ⟨c7r234targets, c7r234choice, ?_, c7r234_checked⟩
  intro S h
  simp only [c7r234targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 3 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 12 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 28 _ (by rfl)))
def c7r235 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r235targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r235choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r235_checked : successorFastRowCheck c7r235targets c7r235 c7r235choice = true := by decide
theorem c7r235_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r235 := by
  refine ⟨c7r235targets, c7r235choice, ?_, c7r235_checked⟩
  intro S h
  simp only [c7r235targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 4 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 2 _ (by rfl)))
def c7r236 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)]
def c7r236targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
def c7r236choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((3,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r236_checked : successorFastRowCheck c7r236targets c7r236 c7r236choice = true := by decide
theorem c7r236_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r236 := by
  refine ⟨c7r236targets, c7r236choice, ?_, c7r236_checked⟩
  intro S h
  simp only [c7r236targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 5 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 6 _ (by rfl)))
def c7r237 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)]
def c7r237targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
def c7r237choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r237_checked : successorFastRowCheck c7r237targets c7r237 c7r237choice = true := by decide
theorem c7r237_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r237 := by
  refine ⟨c7r237targets, c7r237choice, ?_, c7r237_checked⟩
  intro S h
  simp only [c7r237targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 6 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 9 _ (by rfl)))
def c7r238 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)]
def c7r238targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
def c7r238choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r238_checked : successorFastRowCheck c7r238targets c7r238 c7r238choice = true := by decide
theorem c7r238_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r238 := by
  refine ⟨c7r238targets, c7r238choice, ?_, c7r238_checked⟩
  intro S h
  simp only [c7r238targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 11 _ (by rfl)))
def c7r239 : List GridPoint := [(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]
def c7r239targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
def c7r239choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,3),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r239_checked : successorFastRowCheck c7r239targets c7r239 c7r239choice = true := by decide
theorem c7r239_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r239 := by
  refine ⟨c7r239targets, c7r239choice, ?_, c7r239_checked⟩
  intro S h
  simp only [c7r239targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 8 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 13 _ (by rfl)))
def c7r240 : List GridPoint := [(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r240targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r240choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,4),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,2),(4,(0,0))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,5),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r240_checked : successorFastRowCheck c7r240targets c7r240 c7r240choice = true := by decide
theorem c7r240_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r240 := by
  refine ⟨c7r240targets, c7r240choice, ?_, c7r240_checked⟩
  intro S h
  simp only [c7r240targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 9 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 23 _ (by rfl)))
def c7r241 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]
def c7r241targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
def c7r241choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,6),(8,(0,0))),((2,0),(9,(0,0))),((2,1),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r241_checked : successorFastRowCheck c7r241targets c7r241 c7r241choice = true := by decide
theorem c7r241_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r241 := by
  refine ⟨c7r241targets, c7r241choice, ?_, c7r241_checked⟩
  intro S h
  simp only [c7r241targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 31 _ (by rfl)))
def c7r242 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)]
def c7r242targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
def c7r242choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r242_checked : successorFastRowCheck c7r242targets c7r242 c7r242choice = true := by decide
theorem c7r242_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r242 := by
  refine ⟨c7r242targets, c7r242choice, ?_, c7r242_checked⟩
  intro S h
  simp only [c7r242targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 4 _ (by rfl)))
def c7r243 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)]
def c7r243targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
def c7r243choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r243_checked : successorFastRowCheck c7r243targets c7r243 c7r243choice = true := by decide
theorem c7r243_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r243 := by
  refine ⟨c7r243targets, c7r243choice, ?_, c7r243_checked⟩
  intro S h
  simp only [c7r243targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L23_lift _ (familyLookup_sound F8B000L23 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 8 _ (by rfl)))
def c7r244 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)]
def c7r244targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
def c7r244choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r244_checked : successorFastRowCheck c7r244targets c7r244 c7r244choice = true := by decide
theorem c7r244_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r244 := by
  refine ⟨c7r244targets, c7r244choice, ?_, c7r244_checked⟩
  intro S h
  simp only [c7r244targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 11 _ (by rfl)))
def c7r245 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)]
def c7r245targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
def c7r245choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r245_checked : successorFastRowCheck c7r245targets c7r245 c7r245choice = true := by decide
theorem c7r245_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r245 := by
  refine ⟨c7r245targets, c7r245choice, ?_, c7r245_checked⟩
  intro S h
  simp only [c7r245targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 13 _ (by rfl)))
def c7r246 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]
def c7r246targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
def c7r246choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r246_checked : successorFastRowCheck c7r246targets c7r246 c7r246choice = true := by decide
theorem c7r246_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r246 := by
  refine ⟨c7r246targets, c7r246choice, ?_, c7r246_checked⟩
  intro S h
  simp only [c7r246targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 15 _ (by rfl)))
def c7r247 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)]
def c7r247targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
def c7r247choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r247_checked : successorFastRowCheck c7r247targets c7r247 c7r247choice = true := by decide
theorem c7r247_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r247 := by
  refine ⟨c7r247targets, c7r247choice, ?_, c7r247_checked⟩
  intro S h
  simp only [c7r247targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 19 _ (by rfl)))
def c7r248 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)]
def c7r248targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)]]
def c7r248choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r248_checked : successorFastRowCheck c7r248targets c7r248 c7r248choice = true := by decide
theorem c7r248_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r248 := by
  refine ⟨c7r248targets, c7r248choice, ?_, c7r248_checked⟩
  intro S h
  simp only [c7r248targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 22 _ (by rfl)))
def c7r249 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)]
def c7r249targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,3)]]
def c7r249choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r249_checked : successorFastRowCheck c7r249targets c7r249 c7r249choice = true := by decide
theorem c7r249_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r249 := by
  refine ⟨c7r249targets, c7r249choice, ?_, c7r249_checked⟩
  intro S h
  simp only [c7r249targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 25 _ (by rfl)))
def c7r250 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]
def c7r250targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0)],[(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)]]
def c7r250choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,-1),(11,(0,1))),((3,1),(12,(0,0))),((4,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r250_checked : successorFastRowCheck c7r250targets c7r250 c7r250choice = true := by decide
theorem c7r250_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r250 := by
  refine ⟨c7r250targets, c7r250choice, ?_, c7r250_checked⟩
  intro S h
  simp only [c7r250targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 27 _ (by rfl)))
def c7r251 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)]
def c7r251targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
def c7r251choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r251_checked : successorFastRowCheck c7r251targets c7r251 c7r251choice = true := by decide
theorem c7r251_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r251 := by
  refine ⟨c7r251targets, c7r251choice, ?_, c7r251_checked⟩
  intro S h
  simp only [c7r251targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 30 _ (by rfl)))
def c7r252 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)]
def c7r252targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
def c7r252choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r252_checked : successorFastRowCheck c7r252targets c7r252 c7r252choice = true := by decide
theorem c7r252_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r252 := by
  refine ⟨c7r252targets, c7r252choice, ?_, c7r252_checked⟩
  intro S h
  simp only [c7r252targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 1 _ (by rfl)))
def c7r253 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]
def c7r253targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
def c7r253choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r253_checked : successorFastRowCheck c7r253targets c7r253 c7r253choice = true := by decide
theorem c7r253_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r253 := by
  refine ⟨c7r253targets, c7r253choice, ?_, c7r253_checked⟩
  intro S h
  simp only [c7r253targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 4 _ (by rfl)))
def c7r254 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)]
def c7r254targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
def c7r254choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r254_checked : successorFastRowCheck c7r254targets c7r254 c7r254choice = true := by decide
theorem c7r254_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r254 := by
  refine ⟨c7r254targets, c7r254choice, ?_, c7r254_checked⟩
  intro S h
  simp only [c7r254targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 7 _ (by rfl)))
def c7r255 : List GridPoint := [(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]
def c7r255targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
def c7r255choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r255_checked : successorFastRowCheck c7r255targets c7r255 c7r255choice = true := by decide
theorem c7r255_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r255 := by
  refine ⟨c7r255targets, c7r255choice, ?_, c7r255_checked⟩
  intro S h
  simp only [c7r255targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L24_lift _ (familyLookup_sound F8B000L24 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L46_lift _ (familyLookup_sound F8B000L46 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L25_lift _ (familyLookup_sound F8B000L25 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L26_lift _ (familyLookup_sound F8B000L26 [] 10 _ (by rfl)))
theorem C7R00224_closed (row : List GridPoint) (h : FamilyMember row F7B000L7) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L7, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r224_closed
  · subst row; exact c7r225_closed
  · subst row; exact c7r226_closed
  · subst row; exact c7r227_closed
  · subst row; exact c7r228_closed
  · subst row; exact c7r229_closed
  · subst row; exact c7r230_closed
  · subst row; exact c7r231_closed
  · subst row; exact c7r232_closed
  · subst row; exact c7r233_closed
  · subst row; exact c7r234_closed
  · subst row; exact c7r235_closed
  · subst row; exact c7r236_closed
  · subst row; exact c7r237_closed
  · subst row; exact c7r238_closed
  · subst row; exact c7r239_closed
  · subst row; exact c7r240_closed
  · subst row; exact c7r241_closed
  · subst row; exact c7r242_closed
  · subst row; exact c7r243_closed
  · subst row; exact c7r244_closed
  · subst row; exact c7r245_closed
  · subst row; exact c7r246_closed
  · subst row; exact c7r247_closed
  · subst row; exact c7r248_closed
  · subst row; exact c7r249_closed
  · subst row; exact c7r250_closed
  · subst row; exact c7r251_closed
  · subst row; exact c7r252_closed
  · subst row; exact c7r253_closed
  · subst row; exact c7r254_closed
  · subst row; exact c7r255_closed
end Polyomino57
