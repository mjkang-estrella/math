import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

theorem c8r160_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2)] := by
  let c8r160targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,2)]]
  let c8r160choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,0),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r160targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2)] c8r160choice = true := by decide
  refine ⟨c8r160targets, c8r160choice, ?_, checked⟩
  intro S h
  simp only [c8r160targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 9 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 7 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L33_lift _ (familyLookup_sound F9B003L33 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 27 _ (by rfl)))
theorem c8r161_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4)] := by
  let c8r161targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,4)]]
  let c8r161choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,5),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r161targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4)] c8r161choice = true := by decide
  refine ⟨c8r161targets, c8r161choice, ?_, checked⟩
  intro S h
  simp only [c8r161targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 10 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 8 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 31 _ (by rfl)))
theorem c8r162_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2)] := by
  let c8r162targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,2)]]
  let c8r162choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r162targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2)] c8r162choice = true := by decide
  refine ⟨c8r162targets, c8r162choice, ?_, checked⟩
  intro S h
  simp only [c8r162targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 11 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 9 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 2 _ (by rfl)))
theorem c8r163_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3)] := by
  let c8r163targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3),(4,3)]]
  let c8r163choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,1),(9,(0,0))),((2,4),(10,(0,0))),((3,2),(11,(0,0))),((3,4),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r163targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,3)] c8r163choice = true := by decide
  refine ⟨c8r163targets, c8r163choice, ?_, checked⟩
  intro S h
  simp only [c8r163targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 12 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 10 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 4 _ (by rfl)))
theorem c8r164_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2)] := by
  let c8r164targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,2)]]
  let c8r164choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,0),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r164targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2)] c8r164choice = true := by decide
  refine ⟨c8r164targets, c8r164choice, ?_, checked⟩
  intro S h
  simp only [c8r164targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 13 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 11 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 8 _ (by rfl)))
theorem c8r165_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3)] := by
  let c8r165targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,3)]]
  let c8r165choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,4),(12,(0,0))),((4,2),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r165targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3)] c8r165choice = true := by decide
  refine ⟨c8r165targets, c8r165choice, ?_, checked⟩
  intro S h
  simp only [c8r165targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 14 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 12 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 11 _ (by rfl)))
theorem c8r166_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2)] := by
  let c8r166targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,2)]]
  let c8r166choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,3),(8,(0,0))),((2,1),(9,(0,0))),((2,3),(10,(0,0))),((3,1),(11,(0,0))),((3,3),(12,(0,0))),((4,1),(13,(0,0))),((4,3),(14,(0,0))),((5,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r166targets [(0,0),(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2)] c8r166choice = true := by decide
  refine ⟨c8r166targets, c8r166choice, ?_, checked⟩
  intro S h
  simp only [c8r166targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 15 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 13 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 14 _ (by rfl)))
theorem c8r167_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6)] := by
  let c8r167targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,6),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,6)]]
  let c8r167choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,7),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r167targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6)] c8r167choice = true := by decide
  refine ⟨c8r167targets, c8r167choice, ?_, checked⟩
  intro S h
  simp only [c8r167targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 16 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 14 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 19 _ (by rfl)))
theorem c8r168_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3)] := by
  let c8r168targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3)]]
  let c8r168choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,6),(10,(0,0))),((2,2),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r168targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3)] c8r168choice = true := by decide
  refine ⟨c8r168targets, c8r168choice, ?_, checked⟩
  intro S h
  simp only [c8r168targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 17 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 15 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 23 _ (by rfl)))
theorem c8r169_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4)] := by
  let c8r169targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,4)]]
  let c8r169choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,6),(10,(0,0))),((2,3),(11,(0,0))),((2,5),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r169targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4)] c8r169choice = true := by decide
  refine ⟨c8r169targets, c8r169choice, ?_, checked⟩
  intro S h
  simp only [c8r169targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 18 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 16 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 25 _ (by rfl)))
theorem c8r170_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,5)] := by
  let c8r170targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,5),(3,5)]]
  let c8r170choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,2),(9,(0,0))),((1,6),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,6),(13,(0,0))),((3,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r170targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,5)] c8r170choice = true := by decide
  refine ⟨c8r170targets, c8r170choice, ?_, checked⟩
  intro S h
  simp only [c8r170targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 19 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 17 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 27 _ (by rfl)))
theorem c8r171_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3)] := by
  let c8r171targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3)]]
  let c8r171choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,1),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r171targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3)] c8r171choice = true := by decide
  refine ⟨c8r171targets, c8r171choice, ?_, checked⟩
  intro S h
  simp only [c8r171targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 20 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 18 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L16_lift _ (familyLookup_sound F9B004L16 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 31 _ (by rfl)))
theorem c8r172_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4)] := by
  let c8r172targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4)]]
  let c8r172choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,2),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r172targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4)] c8r172choice = true := by decide
  refine ⟨c8r172targets, c8r172choice, ?_, checked⟩
  intro S h
  simp only [c8r172targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 21 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 19 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 2 _ (by rfl)))
theorem c8r173_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3)] := by
  let c8r173targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3)]]
  let c8r173choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r173targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3)] c8r173choice = true := by decide
  refine ⟨c8r173targets, c8r173choice, ?_, checked⟩
  intro S h
  simp only [c8r173targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 22 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 20 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 5 _ (by rfl)))
theorem c8r174_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5)] := by
  let c8r174targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5)]]
  let c8r174choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,3),(10,(0,0))),((2,6),(11,(0,0))),((3,4),(12,(0,0))),((3,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r174targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5)] c8r174choice = true := by decide
  refine ⟨c8r174targets, c8r174choice, ?_, checked⟩
  intro S h
  simp only [c8r174targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 23 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 21 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 13 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L13_lift _ (familyLookup_sound F9B000L13 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 8 _ (by rfl)))
theorem c8r175_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4)] := by
  let c8r175targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4),(4,4)]]
  let c8r175choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,5),(9,(0,0))),((2,3),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,5),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r175targets [(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,4),(3,4)] c8r175choice = true := by decide
  refine ⟨c8r175targets, c8r175choice, ?_, checked⟩
  intro S h
  simp only [c8r175targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 24 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 22 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 14 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 11 _ (by rfl)))
theorem c8r176_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3)] := by
  let c8r176targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,3)]]
  let c8r176choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0))),((3,2),(13,(0,0))),((3,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r176targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3)] c8r176choice = true := by decide
  refine ⟨c8r176targets, c8r176choice, ?_, checked⟩
  intro S h
  simp only [c8r176targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 25 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 23 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 15 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L11_lift _ (familyLookup_sound F9B000L11 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L15_lift _ (familyLookup_sound F9B000L15 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 17 _ (by rfl)))
theorem c8r177_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4)] := by
  let c8r177targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,4)]]
  let c8r177choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,5),(11,(0,0))),((3,2),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r177targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4)] c8r177choice = true := by decide
  refine ⟨c8r177targets, c8r177choice, ?_, checked⟩
  intro S h
  simp only [c8r177targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 26 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 24 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 16 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 21 _ (by rfl)))
theorem c8r178_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2)] := by
  let c8r178targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(4,2)]]
  let c8r178choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0))),((3,3),(13,(0,0))),((4,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r178targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2)] c8r178choice = true := by decide
  refine ⟨c8r178targets, c8r178choice, ?_, checked⟩
  intro S h
  simp only [c8r178targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 27 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 25 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 17 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L7_lift _ (familyLookup_sound F9B000L7 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 24 _ (by rfl)))
theorem c8r179_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3)] := by
  let c8r179targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,3)]]
  let c8r179choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,1),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r179targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3)] c8r179choice = true := by decide
  refine ⟨c8r179targets, c8r179choice, ?_, checked⟩
  intro S h
  simp only [c8r179targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 28 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 26 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 18 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L17_lift _ (familyLookup_sound F9B000L17 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 26 _ (by rfl)))
theorem c8r180_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5)] := by
  let c8r180targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,5),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(3,5)]]
  let c8r180choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,6),(12,(0,0))),((3,3),(13,(0,0))),((3,4),(14,(0,0))),((3,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r180targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5)] c8r180choice = true := by decide
  refine ⟨c8r180targets, c8r180choice, ?_, checked⟩
  intro S h
  simp only [c8r180targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 29 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 27 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 19 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 30 _ (by rfl)))
theorem c8r181_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3)] := by
  let c8r181targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,3)]]
  let c8r181choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,5),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r181targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3)] c8r181choice = true := by decide
  refine ⟨c8r181targets, c8r181choice, ?_, checked⟩
  intro S h
  simp only [c8r181targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 30 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 28 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 1 _ (by rfl)))
theorem c8r182_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,4)] := by
  let c8r182targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,4),(4,4)]]
  let c8r182choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,5),(11,(0,0))),((3,3),(12,(0,0))),((3,5),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r182targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,4)] c8r182choice = true := by decide
  refine ⟨c8r182targets, c8r182choice, ?_, checked⟩
  intro S h
  simp only [c8r182targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L24_lift _ (familyLookup_sound F9B001L24 [] 31 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 29 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 21 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 3 _ (by rfl)))
theorem c8r183_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3)] := by
  let c8r183targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3)]]
  let c8r183choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,1),(12,(0,0))),((3,4),(13,(0,0))),((4,2),(14,(0,0))),((4,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r183targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3)] c8r183choice = true := by decide
  refine ⟨c8r183targets, c8r183choice, ?_, checked⟩
  intro S h
  simp only [c8r183targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 0 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 30 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 22 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 7 _ (by rfl)))
theorem c8r184_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4)] := by
  let c8r184targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,4)]]
  let c8r184choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,5),(13,(0,0))),((4,3),(14,(0,0))),((4,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r184targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4)] c8r184choice = true := by decide
  refine ⟨c8r184targets, c8r184choice, ?_, checked⟩
  intro S h
  simp only [c8r184targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 1 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L32_lift _ (familyLookup_sound F9B002L32 [] 31 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 10 _ (by rfl)))
theorem c8r185_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3)] := by
  let c8r185targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,4),(2,4),(3,4),(4,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3),(5,3)]]
  let c8r185choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((0,-1),(4,(0,1))),((0,4),(5,(0,0))),((1,0),(6,(0,0))),((1,1),(7,(0,0))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,2),(12,(0,0))),((3,4),(13,(0,0))),((4,2),(14,(0,0))),((4,4),(15,(0,0))),((5,3),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r185targets [(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,3),(4,3)] c8r185choice = true := by decide
  refine ⟨c8r185targets, c8r185choice, ?_, checked⟩
  intro S h
  simp only [c8r185targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 2 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 0 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L17_lift _ (familyLookup_sound F9B004L17 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L12_lift _ (familyLookup_sound F9B000L12 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L14_lift _ (familyLookup_sound F9B000L14 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L16_lift _ (familyLookup_sound F9B000L16 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L18_lift _ (familyLookup_sound F9B000L18 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 13 _ (by rfl)))
theorem c8r186_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4)] := by
  let c8r186targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,4),(1,5),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(0,6),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,4)]]
  let c8r186choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,4),(3,(1,0))),((-1,5),(4,(1,0))),((0,-1),(5,(0,1))),((0,3),(6,(0,0))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,5),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r186targets [(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4)] c8r186choice = true := by decide
  refine ⟨c8r186targets, c8r186choice, ?_, checked⟩
  intro S h
  simp only [c8r186targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 3 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 1 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 20 _ (by rfl)))
theorem c8r187_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4)] := by
  let c8r187targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,5),(1,0),(1,1),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,4)]]
  let c8r187choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,1),(8,(0,0))),((1,5),(9,(0,0))),((2,0),(10,(0,0))),((2,2),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r187targets [(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4)] c8r187choice = true := by decide
  refine ⟨c8r187targets, c8r187choice, ?_, checked⟩
  intro S h
  simp only [c8r187targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 4 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 2 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L4_lift _ (familyLookup_sound F9B000L4 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 15 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L59_lift _ (familyLookup_sound F9B001L59 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 26 _ (by rfl)))
theorem c8r188_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4)] := by
  let c8r188targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,4)]]
  let c8r188choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,5),(8,(0,0))),((2,1),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r188targets [(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4)] c8r188choice = true := by decide
  refine ⟨c8r188targets, c8r188choice, ?_, checked⟩
  intro S h
  simp only [c8r188targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 5 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 3 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L5_lift _ (familyLookup_sound F9B000L5 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 31 _ (by rfl)))
theorem c8r189_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5)] := by
  let c8r189targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,5)]]
  let c8r189choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,6),(9,(0,0))),((2,2),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((2,5),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r189targets [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5)] c8r189choice = true := by decide
  refine ⟨c8r189targets, c8r189choice, ?_, checked⟩
  intro S h
  simp only [c8r189targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 6 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 4 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 4 _ (by rfl)))
theorem c8r190_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2)] := by
  let c8r190targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(3,2)]]
  let c8r190choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,5),(9,(0,0))),((2,1),(10,(0,0))),((2,3),(11,(0,0))),((2,4),(12,(0,0))),((3,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r190targets [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2)] c8r190choice = true := by decide
  refine ⟨c8r190targets, c8r190choice, ?_, checked⟩
  intro S h
  simp only [c8r190targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 7 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 5 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L8_lift _ (familyLookup_sound F9B000L8 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 8 _ (by rfl)))
theorem c8r191_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3)] := by
  let c8r191targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3),(3,3)]]
  let c8r191choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,4),(3,(1,0))),((0,-1),(4,(0,1))),((0,3),(5,(0,0))),((0,5),(6,(0,0))),((1,0),(7,(0,0))),((1,1),(8,(0,0))),((1,5),(9,(0,0))),((2,2),(10,(0,0))),((2,4),(11,(0,0))),((3,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r191targets [(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,3)] c8r191choice = true := by decide
  refine ⟨c8r191targets, c8r191choice, ?_, checked⟩
  intro S h
  simp only [c8r191targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L25_lift _ (familyLookup_sound F9B001L25 [] 8 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L33_lift _ (familyLookup_sound F9B002L33 [] 6 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L34_lift _ (familyLookup_sound F9B003L34 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L41_lift _ (familyLookup_sound F9B004L41 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L9_lift _ (familyLookup_sound F9B000L9 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L6_lift _ (familyLookup_sound F9B000L6 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L19_lift _ (familyLookup_sound F9B000L19 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L20_lift _ (familyLookup_sound F9B000L20 [] 10 _ (by rfl)))
theorem C8R00160_closed (row : List GridPoint) (h : FamilyMember row F8B000L5) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L5, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r160_closed
  · subst row; exact c8r161_closed
  · subst row; exact c8r162_closed
  · subst row; exact c8r163_closed
  · subst row; exact c8r164_closed
  · subst row; exact c8r165_closed
  · subst row; exact c8r166_closed
  · subst row; exact c8r167_closed
  · subst row; exact c8r168_closed
  · subst row; exact c8r169_closed
  · subst row; exact c8r170_closed
  · subst row; exact c8r171_closed
  · subst row; exact c8r172_closed
  · subst row; exact c8r173_closed
  · subst row; exact c8r174_closed
  · subst row; exact c8r175_closed
  · subst row; exact c8r176_closed
  · subst row; exact c8r177_closed
  · subst row; exact c8r178_closed
  · subst row; exact c8r179_closed
  · subst row; exact c8r180_closed
  · subst row; exact c8r181_closed
  · subst row; exact c8r182_closed
  · subst row; exact c8r183_closed
  · subst row; exact c8r184_closed
  · subst row; exact c8r185_closed
  · subst row; exact c8r186_closed
  · subst row; exact c8r187_closed
  · subst row; exact c8r188_closed
  · subst row; exact c8r189_closed
  · subst row; exact c8r190_closed
  · subst row; exact c8r191_closed
end Polyomino57
