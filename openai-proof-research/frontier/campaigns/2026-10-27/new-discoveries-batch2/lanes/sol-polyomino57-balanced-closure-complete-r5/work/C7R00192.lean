import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r192 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1)]
def c7r192targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)]]
def c7r192choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r192_checked : successorFastRowCheck c7r192targets c7r192 c7r192choice = true := by decide
theorem c7r192_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r192 := by
  refine ⟨c7r192targets, c7r192choice, ?_, c7r192_checked⟩
  intro S h
  simp only [c7r192targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 20 _ (by rfl)))
def c7r193 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2)]
def c7r193targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)]]
def c7r193choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r193_checked : successorFastRowCheck c7r193targets c7r193 c7r193choice = true := by decide
theorem c7r193_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r193 := by
  refine ⟨c7r193targets, c7r193choice, ?_, c7r193_checked⟩
  intro S h
  simp only [c7r193targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 22 _ (by rfl)))
def c7r194 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1)]
def c7r194targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)]]
def c7r194choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r194_checked : successorFastRowCheck c7r194targets c7r194 c7r194choice = true := by decide
theorem c7r194_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r194 := by
  refine ⟨c7r194targets, c7r194choice, ?_, c7r194_checked⟩
  intro S h
  simp only [c7r194targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 25 _ (by rfl)))
def c7r195 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0)]
def c7r195targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)]]
def c7r195choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r195_checked : successorFastRowCheck c7r195targets c7r195 c7r195choice = true := by decide
theorem c7r195_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r195 := by
  refine ⟨c7r195targets, c7r195choice, ?_, c7r195_checked⟩
  intro S h
  simp only [c7r195targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 27 _ (by rfl)))
def c7r196 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2)]
def c7r196targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]
def c7r196choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r196_checked : successorFastRowCheck c7r196targets c7r196 c7r196choice = true := by decide
theorem c7r196_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r196 := by
  refine ⟨c7r196targets, c7r196choice, ?_, c7r196_checked⟩
  intro S h
  simp only [c7r196targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 30 _ (by rfl)))
def c7r197 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1)]
def c7r197targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)]]
def c7r197choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r197_checked : successorFastRowCheck c7r197targets c7r197 c7r197choice = true := by decide
theorem c7r197_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r197 := by
  refine ⟨c7r197targets, c7r197choice, ?_, c7r197_checked⟩
  intro S h
  simp only [c7r197targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 1 _ (by rfl)))
def c7r198 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4)]
def c7r198targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)]]
def c7r198choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r198_checked : successorFastRowCheck c7r198targets c7r198 c7r198choice = true := by decide
theorem c7r198_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r198 := by
  refine ⟨c7r198targets, c7r198choice, ?_, c7r198_checked⟩
  intro S h
  simp only [c7r198targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 6 _ (by rfl)))
def c7r199 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1)]
def c7r199targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)]]
def c7r199choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,2),(10,(0,0))),((3,3),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r199_checked : successorFastRowCheck c7r199targets c7r199 c7r199choice = true := by decide
theorem c7r199_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r199 := by
  refine ⟨c7r199targets, c7r199choice, ?_, c7r199_checked⟩
  intro S h
  simp only [c7r199targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 10 _ (by rfl)))
def c7r200 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2)]
def c7r200targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)]]
def c7r200choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r200_checked : successorFastRowCheck c7r200targets c7r200 c7r200choice = true := by decide
theorem c7r200_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r200 := by
  refine ⟨c7r200targets, c7r200choice, ?_, c7r200_checked⟩
  intro S h
  simp only [c7r200targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 12 _ (by rfl)))
def c7r201 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3)]
def c7r201targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)]]
def c7r201choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,0),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r201_checked : successorFastRowCheck c7r201targets c7r201 c7r201choice = true := by decide
theorem c7r201_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r201 := by
  refine ⟨c7r201targets, c7r201choice, ?_, c7r201_checked⟩
  intro S h
  simp only [c7r201targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 14 _ (by rfl)))
def c7r202 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1)]
def c7r202targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)]]
def c7r202choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r202_checked : successorFastRowCheck c7r202targets c7r202 c7r202choice = true := by decide
theorem c7r202_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r202 := by
  refine ⟨c7r202targets, c7r202choice, ?_, c7r202_checked⟩
  intro S h
  simp only [c7r202targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 17 _ (by rfl)))
def c7r203 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2)]
def c7r203targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)]]
def c7r203choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r203_checked : successorFastRowCheck c7r203targets c7r203 c7r203choice = true := by decide
theorem c7r203_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r203 := by
  refine ⟨c7r203targets, c7r203choice, ?_, c7r203_checked⟩
  intro S h
  simp only [c7r203targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 20 _ (by rfl)))
def c7r204 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1)]
def c7r204targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)]]
def c7r204choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r204_checked : successorFastRowCheck c7r204targets c7r204 c7r204choice = true := by decide
theorem c7r204_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r204 := by
  refine ⟨c7r204targets, c7r204choice, ?_, c7r204_checked⟩
  intro S h
  simp only [c7r204targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 23 _ (by rfl)))
def c7r205 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3)]
def c7r205targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)]]
def c7r205choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r205_checked : successorFastRowCheck c7r205targets c7r205 c7r205choice = true := by decide
theorem c7r205_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r205 := by
  refine ⟨c7r205targets, c7r205choice, ?_, c7r205_checked⟩
  intro S h
  simp only [c7r205targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 26 _ (by rfl)))
def c7r206 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2)]
def c7r206targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)]]
def c7r206choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r206_checked : successorFastRowCheck c7r206targets c7r206 c7r206choice = true := by decide
theorem c7r206_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r206 := by
  refine ⟨c7r206targets, c7r206choice, ?_, c7r206_checked⟩
  intro S h
  simp only [c7r206targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 29 _ (by rfl)))
def c7r207 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2)]
def c7r207targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)]]
def c7r207choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r207_checked : successorFastRowCheck c7r207targets c7r207 c7r207choice = true := by decide
theorem c7r207_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r207 := by
  refine ⟨c7r207targets, c7r207choice, ?_, c7r207_checked⟩
  intro S h
  simp only [c7r207targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 2 _ (by rfl)))
def c7r208 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0)]
def c7r208targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)]]
def c7r208choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,0),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r208_checked : successorFastRowCheck c7r208targets c7r208 c7r208choice = true := by decide
theorem c7r208_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r208 := by
  refine ⟨c7r208targets, c7r208choice, ?_, c7r208_checked⟩
  intro S h
  simp only [c7r208targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 4 _ (by rfl)))
def c7r209 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1)]
def c7r209targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]
def c7r209choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r209_checked : successorFastRowCheck c7r209targets c7r209 c7r209choice = true := by decide
theorem c7r209_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r209 := by
  refine ⟨c7r209targets, c7r209choice, ?_, c7r209_checked⟩
  intro S h
  simp only [c7r209targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 6 _ (by rfl)))
def c7r210 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3)]
def c7r210targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,3)]]
def c7r210choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((2,3),(8,(0,0))),((3,0),(9,(0,0))),((3,4),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r210_checked : successorFastRowCheck c7r210targets c7r210 c7r210choice = true := by decide
theorem c7r210_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r210 := by
  refine ⟨c7r210targets, c7r210choice, ?_, c7r210_checked⟩
  intro S h
  simp only [c7r210targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 10 _ (by rfl)))
def c7r211 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1)]
def c7r211targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)]]
def c7r211choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r211_checked : successorFastRowCheck c7r211targets c7r211 c7r211choice = true := by decide
theorem c7r211_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r211 := by
  refine ⟨c7r211targets, c7r211choice, ?_, c7r211_checked⟩
  intro S h
  simp only [c7r211targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 13 _ (by rfl)))
def c7r212 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2)]
def c7r212targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2)]]
def c7r212choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r212_checked : successorFastRowCheck c7r212targets c7r212 c7r212choice = true := by decide
theorem c7r212_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r212 := by
  refine ⟨c7r212targets, c7r212choice, ?_, c7r212_checked⟩
  intro S h
  simp only [c7r212targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 15 _ (by rfl)))
def c7r213 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1)]
def c7r213targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)]]
def c7r213choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r213_checked : successorFastRowCheck c7r213targets c7r213 c7r213choice = true := by decide
theorem c7r213_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r213 := by
  refine ⟨c7r213targets, c7r213choice, ?_, c7r213_checked⟩
  intro S h
  simp only [c7r213targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 18 _ (by rfl)))
def c7r214 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2)]
def c7r214targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)]]
def c7r214choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r214_checked : successorFastRowCheck c7r214targets c7r214 c7r214choice = true := by decide
theorem c7r214_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r214 := by
  refine ⟨c7r214targets, c7r214choice, ?_, c7r214_checked⟩
  intro S h
  simp only [c7r214targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 21 _ (by rfl)))
def c7r215 : List GridPoint := [(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1)]
def c7r215targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)]]
def c7r215choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r215_checked : successorFastRowCheck c7r215targets c7r215 c7r215choice = true := by decide
theorem c7r215_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r215 := by
  refine ⟨c7r215targets, c7r215choice, ?_, c7r215_checked⟩
  intro S h
  simp only [c7r215targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L52_lift _ (familyLookup_sound F8B000L52 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L20_lift _ (familyLookup_sound F8B000L20 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 24 _ (by rfl)))
def c7r216 : List GridPoint := [(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)]
def c7r216targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)],[(0,0),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,1),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)]]
def c7r216choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,1),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r216_checked : successorFastRowCheck c7r216targets c7r216 c7r216choice = true := by decide
theorem c7r216_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r216 := by
  refine ⟨c7r216targets, c7r216choice, ?_, c7r216_checked⟩
  intro S h
  simp only [c7r216targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 17 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 7 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L19_lift _ (familyLookup_sound F8B001L19 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L0_lift _ (familyLookup_sound F8B000L0 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 30 _ (by rfl)))
def c7r217 : List GridPoint := [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)]
def c7r217targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,3)]]
def c7r217choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r217_checked : successorFastRowCheck c7r217targets c7r217 c7r217choice = true := by decide
theorem c7r217_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r217 := by
  refine ⟨c7r217targets, c7r217choice, ?_, c7r217_checked⟩
  intro S h
  simp only [c7r217targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 18 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 3 _ (by rfl)))
def c7r218 : List GridPoint := [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)]
def c7r218targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(3,0)]]
def c7r218choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,-1),(8,(0,1))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r218_checked : successorFastRowCheck c7r218targets c7r218 c7r218choice = true := by decide
theorem c7r218_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r218 := by
  refine ⟨c7r218targets, c7r218choice, ?_, c7r218_checked⟩
  intro S h
  simp only [c7r218targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 19 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 6 _ (by rfl)))
def c7r219 : List GridPoint := [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)]
def c7r219targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(3,1)]]
def c7r219choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r219_checked : successorFastRowCheck c7r219targets c7r219 c7r219choice = true := by decide
theorem c7r219_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r219 := by
  refine ⟨c7r219targets, c7r219choice, ?_, c7r219_checked⟩
  intro S h
  simp only [c7r219targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 20 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 8 _ (by rfl)))
def c7r220 : List GridPoint := [(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)]
def c7r220targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,3),(0,4),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)],[(0,1),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,1),(2,2)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(2,3)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2)]]
def c7r220choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((-1,3),(2,(1,0))),((0,-1),(3,(0,1))),((0,1),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,3),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r220_checked : successorFastRowCheck c7r220targets c7r220 c7r220choice = true := by decide
theorem c7r220_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r220 := by
  refine ⟨c7r220targets, c7r220choice, ?_, c7r220_checked⟩
  intro S h
  simp only [c7r220targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 21 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L14_lift _ (familyLookup_sound F8B001L14 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L11_lift _ (familyLookup_sound F8B000L11 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L2_lift _ (familyLookup_sound F8B000L2 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 10 _ (by rfl)))
def c7r221 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)]
def c7r221targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
def c7r221choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,-1),(6,(0,1))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r221_checked : successorFastRowCheck c7r221targets c7r221 c7r221choice = true := by decide
theorem c7r221_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r221 := by
  refine ⟨c7r221targets, c7r221choice, ?_, c7r221_checked⟩
  intro S h
  simp only [c7r221targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 22 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L21_lift _ (familyLookup_sound F8B000L21 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 18 _ (by rfl)))
def c7r222 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)]
def c7r222targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
def c7r222choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r222_checked : successorFastRowCheck c7r222targets c7r222 c7r222choice = true := by decide
theorem c7r222_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r222 := by
  refine ⟨c7r222targets, c7r222choice, ?_, c7r222_checked⟩
  intro S h
  simp only [c7r222targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 23 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L45_lift _ (familyLookup_sound F8B000L45 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 22 _ (by rfl)))
def c7r223 : List GridPoint := [(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)]
def c7r223targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,0),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
def c7r223choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,2),(1,(1,0))),((0,-1),(2,(0,1))),((0,1),(3,(0,0))),((0,3),(4,(0,0))),((1,-1),(5,(0,1))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r223_checked : successorFastRowCheck c7r223targets c7r223 c7r223choice = true := by decide
theorem c7r223_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r223 := by
  refine ⟨c7r223targets, c7r223choice, ?_, c7r223_checked⟩
  intro S h
  simp only [c7r223targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L31_lift _ (familyLookup_sound F8B000L31 [] 24 _ (by rfl)))
  · subst S
    exact F8B001_lift _ (F8B001L3_lift _ (familyLookup_sound F8B001L3 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L6_lift _ (familyLookup_sound F8B000L6 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L44_lift _ (familyLookup_sound F8B000L44 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L22_lift _ (familyLookup_sound F8B000L22 [] 25 _ (by rfl)))
theorem C7R00192_closed (row : List GridPoint) (h : FamilyMember row F7B000L6) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L6, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r192_closed
  · subst row; exact c7r193_closed
  · subst row; exact c7r194_closed
  · subst row; exact c7r195_closed
  · subst row; exact c7r196_closed
  · subst row; exact c7r197_closed
  · subst row; exact c7r198_closed
  · subst row; exact c7r199_closed
  · subst row; exact c7r200_closed
  · subst row; exact c7r201_closed
  · subst row; exact c7r202_closed
  · subst row; exact c7r203_closed
  · subst row; exact c7r204_closed
  · subst row; exact c7r205_closed
  · subst row; exact c7r206_closed
  · subst row; exact c7r207_closed
  · subst row; exact c7r208_closed
  · subst row; exact c7r209_closed
  · subst row; exact c7r210_closed
  · subst row; exact c7r211_closed
  · subst row; exact c7r212_closed
  · subst row; exact c7r213_closed
  · subst row; exact c7r214_closed
  · subst row; exact c7r215_closed
  · subst row; exact c7r216_closed
  · subst row; exact c7r217_closed
  · subst row; exact c7r218_closed
  · subst row; exact c7r219_closed
  · subst row; exact c7r220_closed
  · subst row; exact c7r221_closed
  · subst row; exact c7r222_closed
  · subst row; exact c7r223_closed
end Polyomino57
