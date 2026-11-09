import F9All
import F8B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

theorem c8r0_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7)] := by
  let c8r0targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,7)]]
  let c8r0choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,6),(16,(0,0))),((1,7),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r0targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7)] c8r0choice = true := by decide
  refine ⟨c8r0targets, c8r0choice, ?_, checked⟩
  intro S h
  simp only [c8r0targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 9 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 7 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L28_lift _ (familyLookup_sound F9B003L28 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L38_lift _ (familyLookup_sound F9B004L38 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 8 _ (by rfl)))
theorem c8r1_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0)] := by
  let c8r1targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(2,0)]]
  let c8r1choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,-1),(9,(0,1))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((2,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r1targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0)] c8r1choice = true := by decide
  refine ⟨c8r1targets, c8r1choice, ?_, checked⟩
  intro S h
  simp only [c8r1targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 10 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 8 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 21 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L38_lift _ (familyLookup_sound F9B004L38 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 1 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 15 _ (by rfl)))
theorem c8r2_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1)] := by
  let c8r2targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1)]]
  let c8r2choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r2targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1)] c8r2choice = true := by decide
  refine ⟨c8r2targets, c8r2choice, ?_, checked⟩
  intro S h
  simp only [c8r2targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 11 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 9 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 22 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L38_lift _ (familyLookup_sound F9B004L38 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 21 _ (by rfl)))
theorem c8r3_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2)] := by
  let c8r3targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,2)]]
  let c8r3choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r3targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2)] c8r3choice = true := by decide
  refine ⟨c8r3targets, c8r3choice, ?_, checked⟩
  intro S h
  simp only [c8r3targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 12 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 10 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L38_lift _ (familyLookup_sound F9B004L38 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 26 _ (by rfl)))
theorem c8r4_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3)] := by
  let c8r4targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,3)]]
  let c8r4choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r4targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3)] c8r4choice = true := by decide
  refine ⟨c8r4targets, c8r4choice, ?_, checked⟩
  intro S h
  simp only [c8r4targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 13 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 11 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L38_lift _ (familyLookup_sound F9B004L38 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 30 _ (by rfl)))
theorem c8r5_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4)] := by
  let c8r5targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(2,4)]]
  let c8r5choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((2,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r5targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4)] c8r5choice = true := by decide
  refine ⟨c8r5targets, c8r5choice, ?_, checked⟩
  intro S h
  simp only [c8r5targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 14 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 12 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L38_lift _ (familyLookup_sound F9B004L38 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 1 _ (by rfl)))
theorem c8r6_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5)] := by
  let c8r6targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(2,5)]]
  let c8r6choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,6),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r6targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5)] c8r6choice = true := by decide
  refine ⟨c8r6targets, c8r6choice, ?_, checked⟩
  intro S h
  simp only [c8r6targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 15 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 13 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L38_lift _ (familyLookup_sound F9B004L38 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 3 _ (by rfl)))
theorem c8r7_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6)] := by
  let c8r7targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(2,6)]]
  let c8r7choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((0,-1),(7,(0,1))),((0,7),(8,(0,0))),((1,0),(9,(0,0))),((1,1),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,7),(15,(0,0))),((2,6),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r7targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6)] c8r7choice = true := by decide
  refine ⟨c8r7targets, c8r7choice, ?_, checked⟩
  intro S h
  simp only [c8r7targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 16 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 14 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L38_lift _ (familyLookup_sound F9B004L38 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L53_lift _ (familyLookup_sound F9B004L53 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 5 _ (by rfl)))
theorem c8r8_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1)] := by
  let c8r8targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)]]
  let c8r8choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0))),((2,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r8targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1)] c8r8choice = true := by decide
  refine ⟨c8r8targets, c8r8choice, ?_, checked⟩
  intro S h
  simp only [c8r8targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 17 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 15 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L38_lift _ (familyLookup_sound F9B004L38 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 9 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 11 _ (by rfl)))
theorem c8r9_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2)] := by
  let c8r9targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2)]]
  let c8r9choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0))),((2,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r9targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2)] c8r9choice = true := by decide
  refine ⟨c8r9targets, c8r9choice, ?_, checked⟩
  intro S h
  simp only [c8r9targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 18 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 16 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 10 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 16 _ (by rfl)))
theorem c8r10_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3)] := by
  let c8r10targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3)]]
  let c8r10choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0))),((2,3),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r10targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3)] c8r10choice = true := by decide
  refine ⟨c8r10targets, c8r10choice, ?_, checked⟩
  intro S h
  simp only [c8r10targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 19 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 17 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 11 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 20 _ (by rfl)))
theorem c8r11_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4)] := by
  let c8r11targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4)]]
  let c8r11choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0))),((2,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r11targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4)] c8r11choice = true := by decide
  refine ⟨c8r11targets, c8r11choice, ?_, checked⟩
  intro S h
  simp only [c8r11targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 20 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 18 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L11_lift _ (familyLookup_sound F9B004L11 [] 31 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 12 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 23 _ (by rfl)))
theorem c8r12_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5)] := by
  let c8r12targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,5)]]
  let c8r12choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,6),(13,(0,0))),((2,0),(14,(0,0))),((2,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r12targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5)] c8r12choice = true := by decide
  refine ⟨c8r12targets, c8r12choice, ?_, checked⟩
  intro S h
  simp only [c8r12targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 21 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 19 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 0 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 13 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 26 _ (by rfl)))
theorem c8r13_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0)] := by
  let c8r13targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0),(3,0)]]
  let c8r13choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,-1),(8,(0,1))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((2,-1),(14,(0,1))),((2,1),(15,(0,0))),((3,0),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r13targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(2,0)] c8r13choice = true := by decide
  refine ⟨c8r13targets, c8r13choice, ?_, checked⟩
  intro S h
  simp only [c8r13targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 22 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 20 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 1 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 15 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 25 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 28 _ (by rfl)))
theorem c8r14_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2)] := by
  let c8r14targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2)]]
  let c8r14choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,3),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,1),(12,(0,0))),((2,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r14targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2)] c8r14choice = true := by decide
  refine ⟨c8r14targets, c8r14choice, ?_, checked⟩
  intro S h
  simp only [c8r14targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 23 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 21 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 13 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 2 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 1 _ (by rfl)))
theorem c8r15_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3)] := by
  let c8r15targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,3)]]
  let c8r15choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,2),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,1),(12,(0,0))),((2,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r15targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3)] c8r15choice = true := by decide
  refine ⟨c8r15targets, c8r15choice, ?_, checked⟩
  intro S h
  simp only [c8r15targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 24 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 22 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 14 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 3 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 5 _ (by rfl)))
theorem c8r16_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4)] := by
  let c8r16targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4)]]
  let c8r16choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,1),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r16targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4)] c8r16choice = true := by decide
  refine ⟨c8r16targets, c8r16choice, ?_, checked⟩
  intro S h
  simp only [c8r16targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 25 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 23 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 15 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 4 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 8 _ (by rfl)))
theorem c8r17_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5)] := by
  let c8r17targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,5)]]
  let c8r17choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,6),(12,(0,0))),((2,1),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r17targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5)] c8r17choice = true := by decide
  refine ⟨c8r17targets, c8r17choice, ?_, checked⟩
  intro S h
  simp only [c8r17targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 26 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 24 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 16 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 5 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 11 _ (by rfl)))
theorem c8r18_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1)] := by
  let c8r18targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1),(3,1)]]
  let c8r18choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,2),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,0),(13,(0,0))),((2,2),(14,(0,0))),((3,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r18targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(2,1)] c8r18choice = true := by decide
  refine ⟨c8r18targets, c8r18choice, ?_, checked⟩
  intro S h
  simp only [c8r18targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 27 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 25 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 17 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 6 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 10 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 14 _ (by rfl)))
theorem c8r19_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3)] := by
  let c8r19targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,3)]]
  let c8r19choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,4),(10,(0,0))),((1,5),(11,(0,0))),((2,2),(12,(0,0))),((2,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r19targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3)] c8r19choice = true := by decide
  refine ⟨c8r19targets, c8r19choice, ?_, checked⟩
  intro S h
  simp only [c8r19targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 28 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 26 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 18 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 7 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 18 _ (by rfl)))
theorem c8r20_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4)] := by
  let c8r20targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,4)]]
  let c8r20choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,5),(11,(0,0))),((2,2),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r20targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4)] c8r20choice = true := by decide
  refine ⟨c8r20targets, c8r20choice, ?_, checked⟩
  intro S h
  simp only [c8r20targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 29 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 27 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 19 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 8 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 21 _ (by rfl)))
theorem c8r21_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5)] := by
  let c8r21targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,5)]]
  let c8r21choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,6),(12,(0,0))),((2,2),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r21targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5)] c8r21choice = true := by decide
  refine ⟨c8r21targets, c8r21choice, ?_, checked⟩
  intro S h
  simp only [c8r21targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 30 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 28 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 9 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 24 _ (by rfl)))
theorem c8r22_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2)] := by
  let c8r22targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2),(3,2)]]
  let c8r22choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,3),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,1),(13,(0,0))),((2,3),(14,(0,0))),((3,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r22targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(2,2)] c8r22choice = true := by decide
  refine ⟨c8r22targets, c8r22choice, ?_, checked⟩
  intro S h
  simp only [c8r22targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L19_lift _ (familyLookup_sound F9B001L19 [] 31 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 29 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 21 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 10 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 13 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 27 _ (by rfl)))
theorem c8r23_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4)] := by
  let c8r23targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,4)]]
  let c8r23choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,5),(11,(0,0))),((2,3),(12,(0,0))),((2,4),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r23targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4)] c8r23choice = true := by decide
  refine ⟨c8r23targets, c8r23choice, ?_, checked⟩
  intro S h
  simp only [c8r23targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 0 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 30 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 22 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 11 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 14 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 27 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 17 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 30 _ (by rfl)))
theorem c8r24_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5)] := by
  let c8r24targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,5)]]
  let c8r24choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,4),(11,(0,0))),((1,6),(12,(0,0))),((2,3),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r24targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5)] c8r24choice = true := by decide
  refine ⟨c8r24targets, c8r24choice, ?_, checked⟩
  intro S h
  simp only [c8r24targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 1 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L27_lift _ (familyLookup_sound F9B002L27 [] 31 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 23 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 12 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 15 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 16 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 1 _ (by rfl)))
theorem c8r25_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3)] := by
  let c8r25targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3),(3,3)]]
  let c8r25choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,4),(11,(0,0))),((1,5),(12,(0,0))),((2,2),(13,(0,0))),((2,4),(14,(0,0))),((3,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r25targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(2,3)] c8r25choice = true := by decide
  refine ⟨c8r25targets, c8r25choice, ?_, checked⟩
  intro S h
  simp only [c8r25targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 2 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 0 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 24 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 13 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 16 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 4 _ (by rfl)))
theorem c8r26_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5)] := by
  let c8r26targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,5)]]
  let c8r26choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,6),(12,(0,0))),((2,4),(13,(0,0))),((2,5),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r26targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5)] c8r26choice = true := by decide
  refine ⟨c8r26targets, c8r26choice, ?_, checked⟩
  intro S h
  simp only [c8r26targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 3 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 1 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 25 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 14 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 17 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L50_lift _ (familyLookup_sound F9B004L50 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L0_lift _ (familyLookup_sound F9B000L0 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 28 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 7 _ (by rfl)))
theorem c8r27_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4)] := by
  let c8r27targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4),(3,4)]]
  let c8r27choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,5),(12,(0,0))),((2,3),(13,(0,0))),((2,5),(14,(0,0))),((3,4),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r27targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(2,4)] c8r27choice = true := by decide
  refine ⟨c8r27targets, c8r27choice, ?_, checked⟩
  intro S h
  simp only [c8r27targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 4 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 2 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 26 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 15 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 18 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 0 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 6 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 8 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 10 _ (by rfl)))
theorem c8r28_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6)] := by
  let c8r28targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6),(2,6)]]
  let c8r28choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,7),(13,(0,0))),((2,5),(14,(0,0))),((2,6),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r28targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6)] c8r28choice = true := by decide
  refine ⟨c8r28targets, c8r28choice, ?_, checked⟩
  intro S h
  simp only [c8r28targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 5 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 3 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 27 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 16 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 19 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 4 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 9 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 31 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 13 _ (by rfl)))
theorem c8r29_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,5)] := by
  let c8r29targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,6),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,4),(1,5),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(1,6),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,5),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,5),(3,5)]]
  let c8r29choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((0,-1),(6,(0,1))),((0,6),(7,(0,0))),((1,0),(8,(0,0))),((1,1),(9,(0,0))),((1,2),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,6),(13,(0,0))),((2,4),(14,(0,0))),((2,6),(15,(0,0))),((3,5),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r29targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,5),(2,5)] c8r29choice = true := by decide
  refine ⟨c8r29targets, c8r29choice, ?_, checked⟩
  intro S h
  simp only [c8r29targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 6 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 4 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 28 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 17 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 20 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L51_lift _ (familyLookup_sound F9B004L51 [] 2 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 5 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 3 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 26 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 11 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L2_lift _ (familyLookup_sound F9B000L2 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 1 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 7 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 14 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 15 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 16 _ (by rfl)))
theorem c8r30_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)] := by
  let c8r30targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2)]]
  let c8r30choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,3),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r30targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2)] c8r30choice = true := by decide
  refine ⟨c8r30targets, c8r30choice, ?_, checked⟩
  intro S h
  simp only [c8r30targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 7 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 5 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 29 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 18 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 29 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 6 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 12 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 19 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 20 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 21 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 22 _ (by rfl)))
theorem c8r31_closed : FamilyRowClosed (fun S => FamilyMember S family9) [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3)] := by
  let c8r31targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,3)]]
  let c8r31choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((0,-1),(5,(0,1))),((0,5),(6,(0,0))),((1,-1),(7,(0,1))),((1,2),(8,(0,0))),((1,4),(9,(0,0))),((2,0),(10,(0,0))),((2,1),(11,(0,0))),((2,3),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
  have checked : successorFastRowCheck c8r31targets [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3)] c8r31choice = true := by decide
  refine ⟨c8r31targets, c8r31choice, ?_, checked⟩
  intro S h
  simp only [c8r31targets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    exact F9B001_lift _ (F9B001L20_lift _ (familyLookup_sound F9B001L20 [] 8 _ (by rfl)))
  · subst S
    exact F9B002_lift _ (F9B002L28_lift _ (familyLookup_sound F9B002L28 [] 6 _ (by rfl)))
  · subst S
    exact F9B003_lift _ (F9B003L29_lift _ (familyLookup_sound F9B003L29 [] 30 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L12_lift _ (familyLookup_sound F9B004L12 [] 19 _ (by rfl)))
  · subst S
    exact F9B004_lift _ (F9B004L39_lift _ (familyLookup_sound F9B004L39 [] 22 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 30 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L1_lift _ (familyLookup_sound F9B000L1 [] 7 _ (by rfl)))
  · subst S
    exact F9B001_lift _ (F9B001L55_lift _ (familyLookup_sound F9B001L55 [] 13 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 18 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 23 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 24 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 25 _ (by rfl)))
  · subst S
    exact F9B000_lift _ (F9B000L3_lift _ (familyLookup_sound F9B000L3 [] 26 _ (by rfl)))
theorem C8R00000_closed (row : List GridPoint) (h : FamilyMember row F8B000L0) : FamilyRowClosed (fun S => FamilyMember S family9) row := by
  simp only [F8B000L0, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact c8r0_closed
  · subst row; exact c8r1_closed
  · subst row; exact c8r2_closed
  · subst row; exact c8r3_closed
  · subst row; exact c8r4_closed
  · subst row; exact c8r5_closed
  · subst row; exact c8r6_closed
  · subst row; exact c8r7_closed
  · subst row; exact c8r8_closed
  · subst row; exact c8r9_closed
  · subst row; exact c8r10_closed
  · subst row; exact c8r11_closed
  · subst row; exact c8r12_closed
  · subst row; exact c8r13_closed
  · subst row; exact c8r14_closed
  · subst row; exact c8r15_closed
  · subst row; exact c8r16_closed
  · subst row; exact c8r17_closed
  · subst row; exact c8r18_closed
  · subst row; exact c8r19_closed
  · subst row; exact c8r20_closed
  · subst row; exact c8r21_closed
  · subst row; exact c8r22_closed
  · subst row; exact c8r23_closed
  · subst row; exact c8r24_closed
  · subst row; exact c8r25_closed
  · subst row; exact c8r26_closed
  · subst row; exact c8r27_closed
  · subst row; exact c8r28_closed
  · subst row; exact c8r29_closed
  · subst row; exact c8r30_closed
  · subst row; exact c8r31_closed
end Polyomino57
