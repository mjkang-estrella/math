import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r320 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)]
def c7r320targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
def c7r320choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r320_checked : successorFastRowCheck c7r320targets c7r320 c7r320choice = true := by decide
theorem c7r320_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r320 := by
  refine ⟨c7r320targets, c7r320choice, ?_, c7r320_checked⟩
  intro S h
  simp only [c7r320targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 26 _ (by rfl)))
def c7r321 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)]
def c7r321targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r321choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r321_checked : successorFastRowCheck c7r321targets c7r321 c7r321choice = true := by decide
theorem c7r321_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r321 := by
  refine ⟨c7r321targets, c7r321choice, ?_, c7r321_checked⟩
  intro S h
  simp only [c7r321targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 29 _ (by rfl)))
def c7r322 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)]
def c7r322targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
def c7r322choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r322_checked : successorFastRowCheck c7r322targets c7r322 c7r322choice = true := by decide
theorem c7r322_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r322 := by
  refine ⟨c7r322targets, c7r322choice, ?_, c7r322_checked⟩
  intro S h
  simp only [c7r322targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 0 _ (by rfl)))
def c7r323 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)]
def c7r323targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
def c7r323choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,-1),(11,(0,1))),((4,1),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r323_checked : successorFastRowCheck c7r323targets c7r323 c7r323choice = true := by decide
theorem c7r323_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r323 := by
  refine ⟨c7r323targets, c7r323choice, ?_, c7r323_checked⟩
  intro S h
  simp only [c7r323targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 2 _ (by rfl)))
def c7r324 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)]
def c7r324targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
def c7r324choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r324_checked : successorFastRowCheck c7r324targets c7r324 c7r324choice = true := by decide
theorem c7r324_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r324 := by
  refine ⟨c7r324targets, c7r324choice, ?_, c7r324_checked⟩
  intro S h
  simp only [c7r324targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 5 _ (by rfl)))
def c7r325 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)]
def c7r325targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
def c7r325choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r325_checked : successorFastRowCheck c7r325targets c7r325 c7r325choice = true := by decide
theorem c7r325_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r325 := by
  refine ⟨c7r325targets, c7r325choice, ?_, c7r325_checked⟩
  intro S h
  simp only [c7r325targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 8 _ (by rfl)))
def c7r326 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)]
def c7r326targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
def c7r326choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,4),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r326_checked : successorFastRowCheck c7r326targets c7r326 c7r326choice = true := by decide
theorem c7r326_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r326 := by
  refine ⟨c7r326targets, c7r326choice, ?_, c7r326_checked⟩
  intro S h
  simp only [c7r326targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L28_lift _ (familyLookup_sound F8B000L28 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 11 _ (by rfl)))
def c7r327 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)]
def c7r327targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
def c7r327choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r327_checked : successorFastRowCheck c7r327targets c7r327 c7r327choice = true := by decide
theorem c7r327_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r327 := by
  refine ⟨c7r327targets, c7r327choice, ?_, c7r327_checked⟩
  intro S h
  simp only [c7r327targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 14 _ (by rfl)))
def c7r328 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)]
def c7r328targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
def c7r328choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r328_checked : successorFastRowCheck c7r328targets c7r328 c7r328choice = true := by decide
theorem c7r328_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r328 := by
  refine ⟨c7r328targets, c7r328choice, ?_, c7r328_checked⟩
  intro S h
  simp only [c7r328targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 19 _ (by rfl)))
def c7r329 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)]
def c7r329targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
def c7r329choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r329_checked : successorFastRowCheck c7r329targets c7r329 c7r329choice = true := by decide
theorem c7r329_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r329 := by
  refine ⟨c7r329targets, c7r329choice, ?_, c7r329_checked⟩
  intro S h
  simp only [c7r329targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 21 _ (by rfl)))
def c7r330 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)]
def c7r330targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
def c7r330choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r330_checked : successorFastRowCheck c7r330targets c7r330 c7r330choice = true := by decide
theorem c7r330_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r330 := by
  refine ⟨c7r330targets, c7r330choice, ?_, c7r330_checked⟩
  intro S h
  simp only [c7r330targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 23 _ (by rfl)))
def c7r331 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)]
def c7r331targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
def c7r331choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r331_checked : successorFastRowCheck c7r331targets c7r331 c7r331choice = true := by decide
theorem c7r331_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r331 := by
  refine ⟨c7r331targets, c7r331choice, ?_, c7r331_checked⟩
  intro S h
  simp only [c7r331targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 26 _ (by rfl)))
def c7r332 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)]
def c7r332targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
def c7r332choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r332_checked : successorFastRowCheck c7r332targets c7r332 c7r332choice = true := by decide
theorem c7r332_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r332 := by
  refine ⟨c7r332targets, c7r332choice, ?_, c7r332_checked⟩
  intro S h
  simp only [c7r332targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 28 _ (by rfl)))
def c7r333 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)]
def c7r333targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
def c7r333choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r333_checked : successorFastRowCheck c7r333targets c7r333 c7r333choice = true := by decide
theorem c7r333_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r333 := by
  refine ⟨c7r333targets, c7r333choice, ?_, c7r333_checked⟩
  intro S h
  simp only [c7r333targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 0 _ (by rfl)))
def c7r334 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)]
def c7r334targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
def c7r334choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r334_checked : successorFastRowCheck c7r334targets c7r334 c7r334choice = true := by decide
theorem c7r334_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r334 := by
  refine ⟨c7r334targets, c7r334choice, ?_, c7r334_checked⟩
  intro S h
  simp only [c7r334targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 3 _ (by rfl)))
def c7r335 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)]
def c7r335targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
def c7r335choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,3),(8,(0,0))),((4,1),(9,(0,0))),((4,3),(10,(0,0))),((5,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r335_checked : successorFastRowCheck c7r335targets c7r335 c7r335choice = true := by decide
theorem c7r335_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r335 := by
  refine ⟨c7r335targets, c7r335choice, ?_, c7r335_checked⟩
  intro S h
  simp only [c7r335targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L55_lift _ (familyLookup_sound F8B000L55 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 5 _ (by rfl)))
def c7r336 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)]
def c7r336targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
def c7r336choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r336_checked : successorFastRowCheck c7r336targets c7r336 c7r336choice = true := by decide
theorem c7r336_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r336 := by
  refine ⟨c7r336targets, c7r336choice, ?_, c7r336_checked⟩
  intro S h
  simp only [c7r336targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 8 _ (by rfl)))
def c7r337 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)]
def c7r337targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
def c7r337choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r337_checked : successorFastRowCheck c7r337targets c7r337 c7r337choice = true := by decide
theorem c7r337_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r337 := by
  refine ⟨c7r337targets, c7r337choice, ?_, c7r337_checked⟩
  intro S h
  simp only [c7r337targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 11 _ (by rfl)))
def c7r338 : List GridPoint := [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)]
def c7r338targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
def c7r338choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,2),(6,(0,0))),((3,0),(7,(0,0))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r338_checked : successorFastRowCheck c7r338targets c7r338 c7r338choice = true := by decide
theorem c7r338_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r338 := by
  refine ⟨c7r338targets, c7r338choice, ?_, c7r338_checked⟩
  intro S h
  simp only [c7r338targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 14 _ (by rfl)))
def c7r339 : List GridPoint := [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)]
def c7r339targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
def c7r339choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r339_checked : successorFastRowCheck c7r339targets c7r339 c7r339choice = true := by decide
theorem c7r339_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r339 := by
  refine ⟨c7r339targets, c7r339choice, ?_, c7r339_checked⟩
  intro S h
  simp only [c7r339targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L32_lift _ (familyLookup_sound F8B000L32 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 19 _ (by rfl)))
def c7r340 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)]
def c7r340targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,3)]]
def c7r340choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,-1),(9,(0,1))),((3,4),(10,(0,0))),((4,0),(11,(0,0))),((4,1),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r340_checked : successorFastRowCheck c7r340targets c7r340 c7r340choice = true := by decide
theorem c7r340_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r340 := by
  refine ⟨c7r340targets, c7r340choice, ?_, c7r340_checked⟩
  intro S h
  simp only [c7r340targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 25 _ (by rfl)))
def c7r341 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)]
def c7r341targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)]]
def c7r341choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r341_checked : successorFastRowCheck c7r341targets c7r341 c7r341choice = true := by decide
theorem c7r341_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r341 := by
  refine ⟨c7r341targets, c7r341choice, ?_, c7r341_checked⟩
  intro S h
  simp only [c7r341targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 28 _ (by rfl)))
def c7r342 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)]
def c7r342targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)]]
def c7r342choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r342_checked : successorFastRowCheck c7r342targets c7r342 c7r342choice = true := by decide
theorem c7r342_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r342 := by
  refine ⟨c7r342targets, c7r342choice, ?_, c7r342_checked⟩
  intro S h
  simp only [c7r342targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 30 _ (by rfl)))
def c7r343 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)]
def c7r343targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)]]
def c7r343choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r343_checked : successorFastRowCheck c7r343targets c7r343 c7r343choice = true := by decide
theorem c7r343_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r343 := by
  refine ⟨c7r343targets, c7r343choice, ?_, c7r343_checked⟩
  intro S h
  simp only [c7r343targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 0 _ (by rfl)))
def c7r344 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)]
def c7r344targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)]]
def c7r344choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r344_checked : successorFastRowCheck c7r344targets c7r344 c7r344choice = true := by decide
theorem c7r344_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r344 := by
  refine ⟨c7r344targets, c7r344choice, ?_, c7r344_checked⟩
  intro S h
  simp only [c7r344targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 3 _ (by rfl)))
def c7r345 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)]
def c7r345targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)]]
def c7r345choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r345_checked : successorFastRowCheck c7r345targets c7r345 c7r345choice = true := by decide
theorem c7r345_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r345 := by
  refine ⟨c7r345targets, c7r345choice, ?_, c7r345_checked⟩
  intro S h
  simp only [c7r345targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 5 _ (by rfl)))
def c7r346 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)]
def c7r346targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)]]
def c7r346choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,3),(10,(0,0))),((5,1),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r346_checked : successorFastRowCheck c7r346targets c7r346 c7r346choice = true := by decide
theorem c7r346_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r346 := by
  refine ⟨c7r346targets, c7r346choice, ?_, c7r346_checked⟩
  intro S h
  simp only [c7r346targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 8 _ (by rfl)))
def c7r347 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)]
def c7r347targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)]]
def c7r347choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,2),(8,(0,0))),((4,0),(9,(0,0))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r347_checked : successorFastRowCheck c7r347targets c7r347 c7r347choice = true := by decide
theorem c7r347_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r347 := by
  refine ⟨c7r347targets, c7r347choice, ?_, c7r347_checked⟩
  intro S h
  simp only [c7r347targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L34_lift _ (familyLookup_sound F8B000L34 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 11 _ (by rfl)))
def c7r348 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)]
def c7r348targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)]]
def c7r348choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r348_checked : successorFastRowCheck c7r348targets c7r348 c7r348choice = true := by decide
theorem c7r348_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r348 := by
  refine ⟨c7r348targets, c7r348choice, ?_, c7r348_checked⟩
  intro S h
  simp only [c7r348targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 16 _ (by rfl)))
def c7r349 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)]
def c7r349targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)]]
def c7r349choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,-1),(11,(0,1))),((5,1),(12,(0,0))),((6,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r349_checked : successorFastRowCheck c7r349targets c7r349 c7r349choice = true := by decide
theorem c7r349_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r349 := by
  refine ⟨c7r349targets, c7r349choice, ?_, c7r349_checked⟩
  intro S h
  simp only [c7r349targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 18 _ (by rfl)))
def c7r350 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)]
def c7r350targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)]]
def c7r350choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,2),(10,(0,0))),((5,0),(11,(0,0))),((5,2),(12,(0,0))),((6,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r350_checked : successorFastRowCheck c7r350targets c7r350 c7r350choice = true := by decide
theorem c7r350_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r350 := by
  refine ⟨c7r350targets, c7r350choice, ?_, c7r350_checked⟩
  intro S h
  simp only [c7r350targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L56_lift _ (familyLookup_sound F8B000L56 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 20 _ (by rfl)))
def c7r351 : List GridPoint := [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)]
def c7r351targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)]]
def c7r351choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((0,-1),(1,(0,1))),((0,1),(2,(0,0))),((1,-1),(3,(0,1))),((1,1),(4,(0,0))),((2,-1),(5,(0,1))),((2,1),(6,(0,0))),((3,-1),(7,(0,1))),((3,1),(8,(0,0))),((4,-1),(9,(0,1))),((4,1),(10,(0,0))),((5,-1),(11,(0,1))),((5,2),(12,(0,0))),((6,0),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r351_checked : successorFastRowCheck c7r351targets c7r351 c7r351choice = true := by decide
theorem c7r351_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r351 := by
  refine ⟨c7r351targets, c7r351choice, ?_, c7r351_checked⟩
  intro S h
  simp only [c7r351targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L57_lift _ (familyLookup_sound F8B000L57 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L33_lift _ (familyLookup_sound F8B000L33 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L58_lift _ (familyLookup_sound F8B000L58 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L35_lift _ (familyLookup_sound F8B000L35 [] 23 _ (by rfl)))
theorem C7R00320_closed (row : List GridPoint) (h : FamilyMember row F7B000L10) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L10, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r320_closed
  · subst row; exact c7r321_closed
  · subst row; exact c7r322_closed
  · subst row; exact c7r323_closed
  · subst row; exact c7r324_closed
  · subst row; exact c7r325_closed
  · subst row; exact c7r326_closed
  · subst row; exact c7r327_closed
  · subst row; exact c7r328_closed
  · subst row; exact c7r329_closed
  · subst row; exact c7r330_closed
  · subst row; exact c7r331_closed
  · subst row; exact c7r332_closed
  · subst row; exact c7r333_closed
  · subst row; exact c7r334_closed
  · subst row; exact c7r335_closed
  · subst row; exact c7r336_closed
  · subst row; exact c7r337_closed
  · subst row; exact c7r338_closed
  · subst row; exact c7r339_closed
  · subst row; exact c7r340_closed
  · subst row; exact c7r341_closed
  · subst row; exact c7r342_closed
  · subst row; exact c7r343_closed
  · subst row; exact c7r344_closed
  · subst row; exact c7r345_closed
  · subst row; exact c7r346_closed
  · subst row; exact c7r347_closed
  · subst row; exact c7r348_closed
  · subst row; exact c7r349_closed
  · subst row; exact c7r350_closed
  · subst row; exact c7r351_closed
end Polyomino57
