import F8All
import F7B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def c7r160 : List GridPoint := [(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0)]
def c7r160targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,0),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)]]
def c7r160choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,-1),(4,(0,1))),((1,1),(5,(0,0))),((2,-1),(6,(0,1))),((2,1),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r160_checked : successorFastRowCheck c7r160targets c7r160 c7r160choice = true := by decide
theorem c7r160_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r160 := by
  refine ⟨c7r160targets, c7r160choice, ?_, c7r160_checked⟩
  intro S h
  simp only [c7r160targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L41_lift _ (familyLookup_sound F8B000L41 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L42_lift _ (familyLookup_sound F8B000L42 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L15_lift _ (familyLookup_sound F8B000L15 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 10 _ (by rfl)))
def c7r161 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5)]
def c7r161targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
def c7r161choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,6),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r161_checked : successorFastRowCheck c7r161targets c7r161 c7r161choice = true := by decide
theorem c7r161_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r161 := by
  refine ⟨c7r161targets, c7r161choice, ?_, c7r161_checked⟩
  intro S h
  simp only [c7r161targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 16 _ (by rfl)))
def c7r162 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1)]
def c7r162targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
def c7r162choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,0),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r162_checked : successorFastRowCheck c7r162targets c7r162 c7r162choice = true := by decide
theorem c7r162_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r162 := by
  refine ⟨c7r162targets, c7r162choice, ?_, c7r162_checked⟩
  intro S h
  simp only [c7r162targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 21 _ (by rfl)))
def c7r163 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2)]
def c7r163targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
def c7r163choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,3),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r163_checked : successorFastRowCheck c7r163targets c7r163 c7r163choice = true := by decide
theorem c7r163_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r163 := by
  refine ⟨c7r163targets, c7r163choice, ?_, c7r163_checked⟩
  intro S h
  simp only [c7r163targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 24 _ (by rfl)))
def c7r164 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3)]
def c7r164targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
def c7r164choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,4),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r164_checked : successorFastRowCheck c7r164targets c7r164 c7r164choice = true := by decide
theorem c7r164_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r164 := by
  refine ⟨c7r164targets, c7r164choice, ?_, c7r164_checked⟩
  intro S h
  simp only [c7r164targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 26 _ (by rfl)))
def c7r165 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4)]
def c7r165targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
def c7r165choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,5),(7,(0,0))),((2,1),(8,(0,0))),((2,2),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r165_checked : successorFastRowCheck c7r165targets c7r165 c7r165choice = true := by decide
theorem c7r165_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r165 := by
  refine ⟨c7r165targets, c7r165choice, ?_, c7r165_checked⟩
  intro S h
  simp only [c7r165targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 28 _ (by rfl)))
def c7r166 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1)]
def c7r166targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)]]
def c7r166choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,-1),(7,(0,1))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r166_checked : successorFastRowCheck c7r166targets c7r166 c7r166choice = true := by decide
theorem c7r166_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r166 := by
  refine ⟨c7r166targets, c7r166choice, ?_, c7r166_checked⟩
  intro S h
  simp only [c7r166targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L29_lift _ (familyLookup_sound F8B000L29 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 0 _ (by rfl)))
def c7r167 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2)]
def c7r167targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)]]
def c7r167choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r167_checked : successorFastRowCheck c7r167targets c7r167 c7r167choice = true := by decide
theorem c7r167_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r167 := by
  refine ⟨c7r167targets, c7r167choice, ?_, c7r167_checked⟩
  intro S h
  simp only [c7r167targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 3 _ (by rfl)))
def c7r168 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3)]
def c7r168targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)]]
def c7r168choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r168_checked : successorFastRowCheck c7r168targets c7r168 c7r168choice = true := by decide
theorem c7r168_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r168 := by
  refine ⟨c7r168targets, c7r168choice, ?_, c7r168_checked⟩
  intro S h
  simp only [c7r168targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 6 _ (by rfl)))
def c7r169 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1)]
def c7r169targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)]]
def c7r169choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,2),(8,(0,0))),((2,3),(9,(0,0))),((3,0),(10,(0,0))),((3,2),(11,(0,0))),((4,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r169_checked : successorFastRowCheck c7r169targets c7r169 c7r169choice = true := by decide
theorem c7r169_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r169 := by
  refine ⟨c7r169targets, c7r169choice, ?_, c7r169_checked⟩
  intro S h
  simp only [c7r169targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 9 _ (by rfl)))
def c7r170 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3)]
def c7r170targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]]
def c7r170choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,4),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r170_checked : successorFastRowCheck c7r170targets c7r170 c7r170choice = true := by decide
theorem c7r170_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r170 := by
  refine ⟨c7r170targets, c7r170choice, ?_, c7r170_checked⟩
  intro S h
  simp only [c7r170targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 12 _ (by rfl)))
def c7r171 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2)]
def c7r171targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)]]
def c7r171choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,3),(8,(0,0))),((3,1),(9,(0,0))),((3,3),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r171_checked : successorFastRowCheck c7r171targets c7r171 c7r171choice = true := by decide
theorem c7r171_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r171 := by
  refine ⟨c7r171targets, c7r171choice, ?_, c7r171_checked⟩
  intro S h
  simp only [c7r171targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 15 _ (by rfl)))
def c7r172 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4)]
def c7r172targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)]]
def c7r172choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,5),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r172_checked : successorFastRowCheck c7r172targets c7r172 c7r172choice = true := by decide
theorem c7r172_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r172 := by
  refine ⟨c7r172targets, c7r172choice, ?_, c7r172_checked⟩
  intro S h
  simp only [c7r172targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L50_lift _ (familyLookup_sound F8B000L50 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 18 _ (by rfl)))
def c7r173 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3)]
def c7r173targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(0,3),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)]]
def c7r173choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,2),(8,(0,0))),((2,4),(9,(0,0))),((3,2),(10,(0,0))),((3,4),(11,(0,0))),((4,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r173_checked : successorFastRowCheck c7r173targets c7r173 c7r173choice = true := by decide
theorem c7r173_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r173 := by
  refine ⟨c7r173targets, c7r173choice, ?_, c7r173_checked⟩
  intro S h
  simp only [c7r173targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 21 _ (by rfl)))
def c7r174 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2)]
def c7r174targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)]]
def c7r174choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,1),(9,(0,0))),((3,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r174_checked : successorFastRowCheck c7r174targets c7r174 c7r174choice = true := by decide
theorem c7r174_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r174 := by
  refine ⟨c7r174targets, c7r174choice, ?_, c7r174_checked⟩
  intro S h
  simp only [c7r174targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 26 _ (by rfl)))
def c7r175 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0)]
def c7r175targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)]]
def c7r175choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((4,0),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r175_checked : successorFastRowCheck c7r175targets c7r175 c7r175choice = true := by decide
theorem c7r175_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r175 := by
  refine ⟨c7r175targets, c7r175choice, ?_, c7r175_checked⟩
  intro S h
  simp only [c7r175targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L16_lift _ (familyLookup_sound F8B000L16 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 28 _ (by rfl)))
def c7r176 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1)]
def c7r176targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
def c7r176choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,-1),(6,(0,1))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r176_checked : successorFastRowCheck c7r176targets c7r176 c7r176choice = true := by decide
theorem c7r176_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r176 := by
  refine ⟨c7r176targets, c7r176choice, ?_, c7r176_checked⟩
  intro S h
  simp only [c7r176targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 30 _ (by rfl)))
def c7r177 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3)]
def c7r177targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)]]
def c7r177choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r177_checked : successorFastRowCheck c7r177targets c7r177 c7r177choice = true := by decide
theorem c7r177_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r177 := by
  refine ⟨c7r177targets, c7r177choice, ?_, c7r177_checked⟩
  intro S h
  simp only [c7r177targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 2 _ (by rfl)))
def c7r178 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1)]
def c7r178targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]
def c7r178choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,1),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r178_checked : successorFastRowCheck c7r178targets c7r178 c7r178choice = true := by decide
theorem c7r178_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r178 := by
  refine ⟨c7r178targets, c7r178choice, ?_, c7r178_checked⟩
  intro S h
  simp only [c7r178targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 5 _ (by rfl)))
def c7r179 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2)]
def c7r179targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]
def c7r179choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r179_checked : successorFastRowCheck c7r179targets c7r179 c7r179choice = true := by decide
theorem c7r179_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r179 := by
  refine ⟨c7r179targets, c7r179choice, ?_, c7r179_checked⟩
  intro S h
  simp only [c7r179targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 7 _ (by rfl)))
def c7r180 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1)]
def c7r180targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
def c7r180choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r180_checked : successorFastRowCheck c7r180targets c7r180 c7r180choice = true := by decide
theorem c7r180_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r180 := by
  refine ⟨c7r180targets, c7r180choice, ?_, c7r180_checked⟩
  intro S h
  simp only [c7r180targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 10 _ (by rfl)))
def c7r181 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2)]
def c7r181targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]
def c7r181choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r181_checked : successorFastRowCheck c7r181targets c7r181 c7r181choice = true := by decide
theorem c7r181_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r181 := by
  refine ⟨c7r181targets, c7r181choice, ?_, c7r181_checked⟩
  intro S h
  simp only [c7r181targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 13 _ (by rfl)))
def c7r182 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1)]
def c7r182targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)]]
def c7r182choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,0),(6,(0,0))),((2,2),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r182_checked : successorFastRowCheck c7r182targets c7r182 c7r182choice = true := by decide
theorem c7r182_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r182 := by
  refine ⟨c7r182targets, c7r182choice, ?_, c7r182_checked⟩
  intro S h
  simp only [c7r182targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 9 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 16 _ (by rfl)))
def c7r183 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4)]
def c7r183targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)]]
def c7r183choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((1,4),(6,(0,0))),((2,1),(7,(0,0))),((2,5),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((3,4),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r183_checked : successorFastRowCheck c7r183targets c7r183 c7r183choice = true := by decide
theorem c7r183_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r183 := by
  refine ⟨c7r183targets, c7r183choice, ?_, c7r183_checked⟩
  intro S h
  simp only [c7r183targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 10 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 20 _ (by rfl)))
def c7r184 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2)]
def c7r184targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]
def c7r184choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,2),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r184_checked : successorFastRowCheck c7r184targets c7r184 c7r184choice = true := by decide
theorem c7r184_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r184 := by
  refine ⟨c7r184targets, c7r184choice, ?_, c7r184_checked⟩
  intro S h
  simp only [c7r184targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 23 _ (by rfl)))
def c7r185 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3)]
def c7r185targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)]]
def c7r185choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,4),(7,(0,0))),((3,2),(8,(0,0))),((3,4),(9,(0,0))),((4,3),(10,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r185_checked : successorFastRowCheck c7r185targets c7r185 c7r185choice = true := by decide
theorem c7r185_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r185 := by
  refine ⟨c7r185targets, c7r185choice, ?_, c7r185_checked⟩
  intro S h
  simp only [c7r185targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 25 _ (by rfl)))
def c7r186 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2)]
def c7r186targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]
def c7r186choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r186_checked : successorFastRowCheck c7r186targets c7r186 c7r186choice = true := by decide
theorem c7r186_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r186 := by
  refine ⟨c7r186targets, c7r186choice, ?_, c7r186_checked⟩
  intro S h
  simp only [c7r186targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 26 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 28 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 29 _ (by rfl)))
def c7r187 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3)]
def c7r187targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)]]
def c7r187choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,2),(10,(0,0))),((4,3),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r187_checked : successorFastRowCheck c7r187targets c7r187 c7r187choice = true := by decide
theorem c7r187_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r187 := by
  refine ⟨c7r187targets, c7r187choice, ?_, c7r187_checked⟩
  intro S h
  simp only [c7r187targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 20 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L8_lift _ (familyLookup_sound F8B000L8 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 27 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 0 _ (by rfl)))
def c7r188 : List GridPoint := [(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2)]
def c7r188targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)]]
def c7r188choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,3),(5,(0,0))),((2,1),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r188_checked : successorFastRowCheck c7r188targets c7r188 c7r188choice = true := by decide
theorem c7r188_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r188 := by
  refine ⟨c7r188targets, c7r188choice, ?_, c7r188_checked⟩
  intro S h
  simp only [c7r188targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 21 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L13_lift _ (familyLookup_sound F8B000L13 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 15 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 29 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L18_lift _ (familyLookup_sound F8B000L18 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 3 _ (by rfl)))
def c7r189 : List GridPoint := [(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3)]
def c7r189targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
def c7r189choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((0,3),(4,(0,0))),((1,0),(5,(0,0))),((1,2),(6,(0,0))),((1,4),(7,(0,0))),((2,0),(8,(0,0))),((2,4),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r189_checked : successorFastRowCheck c7r189targets c7r189 c7r189choice = true := by decide
theorem c7r189_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r189 := by
  refine ⟨c7r189targets, c7r189choice, ?_, c7r189_checked⟩
  intro S h
  simp only [c7r189targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 22 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 25 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L12_lift _ (familyLookup_sound F8B000L12 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 0 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 4 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 6 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 7 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 8 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 9 _ (by rfl)))
def c7r190 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3)]
def c7r190targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,3)]]
def c7r190choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,3),(6,(0,0))),((2,-1),(7,(0,1))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,1),(10,(0,0))),((3,2),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r190_checked : successorFastRowCheck c7r190targets c7r190 c7r190choice = true := by decide
theorem c7r190_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r190 := by
  refine ⟨c7r190targets, c7r190choice, ?_, c7r190_checked⟩
  intro S h
  simp only [c7r190targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 1 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 23 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 5 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 11 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 13 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 14 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 15 _ (by rfl)))
def c7r191 : List GridPoint := [(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0)]
def c7r191targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0)],[(0,0),(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0)]]
def c7r191choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,-1),(6,(0,1))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,1),(9,(0,0))),((3,2),(10,(0,0))),((4,0),(11,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
theorem c7r191_checked : successorFastRowCheck c7r191targets c7r191 c7r191choice = true := by decide
theorem c7r191_closed : FamilyRowClosed (fun S => FamilyMember S family8) c7r191 := by
  refine ⟨c7r191targets, c7r191choice, ?_, c7r191_checked⟩
  intro S h
  simp only [c7r191targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F8B000_lift _ (F8B000L30_lift _ (familyLookup_sound F8B000L30 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L51_lift _ (familyLookup_sound F8B000L51 [] 18 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L10_lift _ (familyLookup_sound F8B000L10 [] 31 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L9_lift _ (familyLookup_sound F8B000L9 [] 3 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L14_lift _ (familyLookup_sound F8B000L14 [] 2 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L17_lift _ (familyLookup_sound F8B000L17 [] 24 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 19 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 12 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L43_lift _ (familyLookup_sound F8B000L43 [] 30 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 16 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 17 _ (by rfl)))
  · subst S
    exact F8B000_lift _ (F8B000L19_lift _ (familyLookup_sound F8B000L19 [] 18 _ (by rfl)))
theorem C7R00160_closed (row : List GridPoint) (h : FamilyMember row F7B000L5) : FamilyRowClosed (fun S => FamilyMember S family8) row := by
  simp only [F7B000L5, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c7r160_closed
  · subst row; exact c7r161_closed
  · subst row; exact c7r162_closed
  · subst row; exact c7r163_closed
  · subst row; exact c7r164_closed
  · subst row; exact c7r165_closed
  · subst row; exact c7r166_closed
  · subst row; exact c7r167_closed
  · subst row; exact c7r168_closed
  · subst row; exact c7r169_closed
  · subst row; exact c7r170_closed
  · subst row; exact c7r171_closed
  · subst row; exact c7r172_closed
  · subst row; exact c7r173_closed
  · subst row; exact c7r174_closed
  · subst row; exact c7r175_closed
  · subst row; exact c7r176_closed
  · subst row; exact c7r177_closed
  · subst row; exact c7r178_closed
  · subst row; exact c7r179_closed
  · subst row; exact c7r180_closed
  · subst row; exact c7r181_closed
  · subst row; exact c7r182_closed
  · subst row; exact c7r183_closed
  · subst row; exact c7r184_closed
  · subst row; exact c7r185_closed
  · subst row; exact c7r186_closed
  · subst row; exact c7r187_closed
  · subst row; exact c7r188_closed
  · subst row; exact c7r189_closed
  · subst row; exact c7r190_closed
  · subst row; exact c7r191_closed
end Polyomino57
