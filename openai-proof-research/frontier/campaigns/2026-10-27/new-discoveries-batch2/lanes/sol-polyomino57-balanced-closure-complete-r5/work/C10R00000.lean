import F11All
import F10B000
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C10R00000G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r0_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9)] := by
    let c10r0targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,9),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,9)]]
    let c10r0choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((-1,9),(9,(1,0))),((0,-1),(10,(0,1))),((0,10),(11,(0,0))),((1,0),(12,(0,0))),((1,1),(13,(0,0))),((1,2),(14,(0,0))),((1,3),(15,(0,0))),((1,4),(16,(0,0))),((1,5),(17,(0,0))),((1,6),(18,(0,0))),((1,7),(19,(0,0))),((1,8),(20,(0,0))),((1,9),(21,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r0targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9)] c10r0choice = true := by decide
    refine ⟨c10r0targets, c10r0choice, ?_, checked⟩
    intro S h
    simp only [c10r0targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L26_lift _ (familyLookup_sound F11B015L26 [] 23 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 4 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 22 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 2 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L2_lift _ (familyLookup_sound F11B060L2 [] 24 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 6 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 0 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 1 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 17 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L3_lift _ (familyLookup_sound F11B066L3 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 8 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 10 _ (by rfl)))
  have c10r1_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0)] := by
    let c10r1targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(2,0)]]
    let c10r1choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,-1),(11,(0,1))),((1,1),(12,(0,0))),((1,2),(13,(0,0))),((1,3),(14,(0,0))),((1,4),(15,(0,0))),((1,5),(16,(0,0))),((1,6),(17,(0,0))),((1,7),(18,(0,0))),((1,8),(19,(0,0))),((2,0),(20,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r1targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0)] c10r1choice = true := by decide
    refine ⟨c10r1targets, c10r1choice, ?_, checked⟩
    intro S h
    simp only [c10r1targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L26_lift _ (familyLookup_sound F11B015L26 [] 24 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 5 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 23 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 3 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L2_lift _ (familyLookup_sound F11B060L2 [] 25 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 7 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 1 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 2 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 18 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 1 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 11 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 12 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 13 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 16 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 18 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 19 _ (by rfl)))
  have c10r2_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1)] := by
    let c10r2targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(2,1)]]
    let c10r2choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,0),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,6),(16,(0,0))),((1,7),(17,(0,0))),((1,8),(18,(0,0))),((2,1),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r2targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1)] c10r2choice = true := by decide
    refine ⟨c10r2targets, c10r2choice, ?_, checked⟩
    intro S h
    simp only [c10r2targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L26_lift _ (familyLookup_sound F11B015L26 [] 25 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 6 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 24 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 4 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L2_lift _ (familyLookup_sound F11B060L2 [] 26 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 8 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 2 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 3 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 11 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 22 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 26 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 27 _ (by rfl)))
  have c10r3_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2)] := by
    let c10r3targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,2)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,2)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(2,2)]]
    let c10r3choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,0),(11,(0,0))),((1,1),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,6),(16,(0,0))),((1,7),(17,(0,0))),((1,8),(18,(0,0))),((2,2),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r3targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2)] c10r3choice = true := by decide
    refine ⟨c10r3targets, c10r3choice, ?_, checked⟩
    intro S h
    simp only [c10r3targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L26_lift _ (familyLookup_sound F11B015L26 [] 26 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 7 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 25 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 5 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L2_lift _ (familyLookup_sound F11B060L2 [] 27 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 9 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 3 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 4 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 12 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 28 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 29 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 2 _ (by rfl)))
  have c10r4_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3)] := by
    let c10r4targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(2,3)]]
    let c10r4choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,0),(11,(0,0))),((1,1),(12,(0,0))),((1,2),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,6),(16,(0,0))),((1,7),(17,(0,0))),((1,8),(18,(0,0))),((2,3),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r4targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3)] c10r4choice = true := by decide
    refine ⟨c10r4targets, c10r4choice, ?_, checked⟩
    intro S h
    simp only [c10r4targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L26_lift _ (familyLookup_sound F11B015L26 [] 27 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 8 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 26 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 6 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L2_lift _ (familyLookup_sound F11B060L2 [] 28 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 10 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 4 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 5 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 13 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 28 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 8 _ (by rfl)))
  have c10r5_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4)] := by
    let c10r5targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(2,4)]]
    let c10r5choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,0),(11,(0,0))),((1,1),(12,(0,0))),((1,2),(13,(0,0))),((1,3),(14,(0,0))),((1,5),(15,(0,0))),((1,6),(16,(0,0))),((1,7),(17,(0,0))),((1,8),(18,(0,0))),((2,4),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r5targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4)] c10r5choice = true := by decide
    refine ⟨c10r5targets, c10r5choice, ?_, checked⟩
    intro S h
    simp only [c10r5targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L26_lift _ (familyLookup_sound F11B015L26 [] 28 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 9 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 27 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 7 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L2_lift _ (familyLookup_sound F11B060L2 [] 29 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 11 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 5 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 6 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 22 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 22 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 29 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 10 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 11 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 12 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 13 _ (by rfl)))
  have c10r6_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5)] := by
    let c10r6targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(2,5)]]
    let c10r6choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,0),(11,(0,0))),((1,1),(12,(0,0))),((1,2),(13,(0,0))),((1,3),(14,(0,0))),((1,4),(15,(0,0))),((1,6),(16,(0,0))),((1,7),(17,(0,0))),((1,8),(18,(0,0))),((2,5),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r6targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5)] c10r6choice = true := by decide
    refine ⟨c10r6targets, c10r6choice, ?_, checked⟩
    intro S h
    simp only [c10r6targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L26_lift _ (familyLookup_sound F11B015L26 [] 29 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 10 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 28 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 8 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L2_lift _ (familyLookup_sound F11B060L2 [] 30 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 12 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 6 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 7 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 16 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 17 _ (by rfl)))
  have c10r7_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6)] := by
    let c10r7targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(2,6)]]
    let c10r7choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,0),(11,(0,0))),((1,1),(12,(0,0))),((1,2),(13,(0,0))),((1,3),(14,(0,0))),((1,4),(15,(0,0))),((1,5),(16,(0,0))),((1,7),(17,(0,0))),((1,8),(18,(0,0))),((2,6),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r7targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6)] c10r7choice = true := by decide
    refine ⟨c10r7targets, c10r7choice, ?_, checked⟩
    intro S h
    simp only [c10r7targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L26_lift _ (familyLookup_sound F11B015L26 [] 30 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 11 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 29 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 9 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L2_lift _ (familyLookup_sound F11B060L2 [] 31 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 13 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 7 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 8 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 8 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 16 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 10 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 18 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 20 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r0_closed
  · subst row; exact c10r1_closed
  · subst row; exact c10r2_closed
  · subst row; exact c10r3_closed
  · subst row; exact c10r4_closed
  · subst row; exact c10r5_closed
  · subst row; exact c10r6_closed
  · subst row; exact c10r7_closed
theorem C10R00000G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r8_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7)] := by
    let c10r8targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(2,7)]]
    let c10r8choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,0),(11,(0,0))),((1,1),(12,(0,0))),((1,2),(13,(0,0))),((1,3),(14,(0,0))),((1,4),(15,(0,0))),((1,5),(16,(0,0))),((1,6),(17,(0,0))),((1,8),(18,(0,0))),((2,7),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r8targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7)] c10r8choice = true := by decide
    refine ⟨c10r8targets, c10r8choice, ?_, checked⟩
    intro S h
    simp only [c10r8targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L26_lift _ (familyLookup_sound F11B015L26 [] 31 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 12 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 30 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 10 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 0 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 14 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 8 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 9 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 8 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 11 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 18 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 22 _ (by rfl)))
  have c10r9_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8)] := by
    let c10r9targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,8),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,9)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,5),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,6),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(1,9)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8),(2,8)]]
    let c10r9choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((-1,8),(8,(1,0))),((0,-1),(9,(0,1))),((0,9),(10,(0,0))),((1,0),(11,(0,0))),((1,1),(12,(0,0))),((1,2),(13,(0,0))),((1,3),(14,(0,0))),((1,4),(15,(0,0))),((1,5),(16,(0,0))),((1,6),(17,(0,0))),((1,7),(18,(0,0))),((1,9),(19,(0,0))),((2,8),(20,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r9targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,8)] c10r9choice = true := by decide
    refine ⟨c10r9targets, c10r9choice, ?_, checked⟩
    intro S h
    simp only [c10r9targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 0 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 13 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L45_lift _ (familyLookup_sound F11B042L45 [] 31 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 11 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 1 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 15 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 9 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 10 _ (by rfl)))
    · subst S
      exact F11B066_lift _ (F11B066L2_lift _ (familyLookup_sound F11B066L2 [] 26 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 10 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 18 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 26 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 12 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 16 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 24 _ (by rfl)))
  have c10r10_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1)] := by
    let c10r10targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,1)]]
    let c10r10choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,-1),(10,(0,1))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,0),(17,(0,0))),((2,1),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r10targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1)] c10r10choice = true := by decide
    refine ⟨c10r10targets, c10r10choice, ?_, checked⟩
    intro S h
    simp only [c10r10targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 1 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 14 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 0 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 12 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 2 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 16 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 10 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 11 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 11 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 26 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 27 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 28 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 29 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 0 _ (by rfl)))
  have c10r11_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2)] := by
    let c10r11targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,2)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,2)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(2,2)]]
    let c10r11choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,-1),(10,(0,1))),((1,1),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,0),(17,(0,0))),((2,2),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r11targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2)] c10r11choice = true := by decide
    refine ⟨c10r11targets, c10r11choice, ?_, checked⟩
    intro S h
    simp only [c10r11targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 2 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 15 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 1 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 13 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 3 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 17 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 11 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 12 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 12 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 16 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 7 _ (by rfl)))
  have c10r12_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3)] := by
    let c10r12targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,3)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,3)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(2,3)]]
    let c10r12choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,-1),(10,(0,1))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,0),(17,(0,0))),((2,3),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r12targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3)] c10r12choice = true := by decide
    refine ⟨c10r12targets, c10r12choice, ?_, checked⟩
    intro S h
    simp only [c10r12targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 3 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 16 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 2 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 14 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 4 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 18 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 12 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 13 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 22 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 13 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 26 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 8 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 10 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 11 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 12 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 13 _ (by rfl)))
  have c10r13_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4)] := by
    let c10r13targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,4)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4),(2,4)]]
    let c10r13choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,-1),(10,(0,1))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,0),(17,(0,0))),((2,4),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r13targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4)] c10r13choice = true := by decide
    refine ⟨c10r13targets, c10r13choice, ?_, checked⟩
    intro S h
    simp only [c10r13targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 4 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 17 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 3 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 15 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 5 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 19 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 13 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 14 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 18 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 27 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 8 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 16 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 18 _ (by rfl)))
  have c10r14_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5)] := by
    let c10r14targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,5)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,5)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5),(2,5)]]
    let c10r14choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,-1),(10,(0,1))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,0),(17,(0,0))),((2,5),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r14targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5)] c10r14choice = true := by decide
    refine ⟨c10r14targets, c10r14choice, ?_, checked⟩
    intro S h
    simp only [c10r14targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 5 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 18 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 4 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 16 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 6 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 20 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 14 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 15 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 28 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 22 _ (by rfl)))
  have c10r15_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6)] := by
    let c10r15targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,6)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,6)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6),(2,6)]]
    let c10r15choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,-1),(10,(0,1))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,7),(16,(0,0))),((2,0),(17,(0,0))),((2,6),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r15targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6)] c10r15choice = true := by decide
    refine ⟨c10r15targets, c10r15choice, ?_, checked⟩
    intro S h
    simp only [c10r15targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 6 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 19 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 5 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 17 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 7 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 21 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 15 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 16 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 16 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 29 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 10 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 25 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r8_closed
  · subst row; exact c10r9_closed
  · subst row; exact c10r10_closed
  · subst row; exact c10r11_closed
  · subst row; exact c10r12_closed
  · subst row; exact c10r13_closed
  · subst row; exact c10r14_closed
  · subst row; exact c10r15_closed
theorem C10R00000G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r16_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,7)] := by
    let c10r16targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,7)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,7)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,7)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,7),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,7),(2,7)]]
    let c10r16choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,-1),(10,(0,1))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,6),(16,(0,0))),((1,8),(17,(0,0))),((2,0),(18,(0,0))),((2,7),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r16targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,7)] c10r16choice = true := by decide
    refine ⟨c10r16targets, c10r16choice, ?_, checked⟩
    intro S h
    simp only [c10r16targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 7 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 20 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 6 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 18 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 8 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 22 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 16 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 26 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 17 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 11 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 16 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 26 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 27 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 28 _ (by rfl)))
  have c10r17_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(2,0)] := by
    let c10r17targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(3,0)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(3,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(3,0)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(3,0)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(3,0)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(3,0)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(3,0)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(3,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,4),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,5),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,6),(2,0)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,7),(2,0)],[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(2,0),(3,0)]]
    let c10r17choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,-1),(10,(0,1))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,3),(13,(0,0))),((1,4),(14,(0,0))),((1,5),(15,(0,0))),((1,6),(16,(0,0))),((1,7),(17,(0,0))),((2,-1),(18,(0,1))),((2,1),(19,(0,0))),((3,0),(20,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r17targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(2,0)] c10r17choice = true := by decide
    refine ⟨c10r17targets, c10r17choice, ?_, checked⟩
    intro S h
    simp only [c10r17targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 8 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 21 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 7 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 19 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 9 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 23 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 17 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 18 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 27 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 19 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 12 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 27 _ (by rfl)))
    · subst S
      exact F11B021_lift _ (F11B021L46_lift _ (familyLookup_sound F11B021L46 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 29 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 30 _ (by rfl)))
  have c10r18_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2)] := by
    let c10r18targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(2,2)]]
    let c10r18choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,3),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((1,7),(15,(0,0))),((2,1),(16,(0,0))),((2,2),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r18targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2)] c10r18choice = true := by decide
    refine ⟨c10r18targets, c10r18choice, ?_, checked⟩
    intro S h
    simp only [c10r18targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 9 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 22 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 8 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 20 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 10 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 24 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 18 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 28 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 5 _ (by rfl)))
  have c10r19_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3)] := by
    let c10r19targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,3)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(2,3)]]
    let c10r19choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,2),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((1,7),(15,(0,0))),((2,1),(16,(0,0))),((2,3),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r19targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3)] c10r19choice = true := by decide
    refine ⟨c10r19targets, c10r19choice, ?_, checked⟩
    intro S h
    simp only [c10r19targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 10 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 23 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 9 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 21 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 11 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 25 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 19 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 29 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 26 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 8 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 10 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 11 _ (by rfl)))
  have c10r20_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4)] := by
    let c10r20targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,4)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4),(2,4)]]
    let c10r20choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((1,7),(15,(0,0))),((2,1),(16,(0,0))),((2,4),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r20targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4)] c10r20choice = true := by decide
    refine ⟨c10r20targets, c10r20choice, ?_, checked⟩
    intro S h
    simp only [c10r20targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 11 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 24 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 10 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 22 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 12 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 26 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 20 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 22 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 27 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 12 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 13 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 16 _ (by rfl)))
  have c10r21_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5)] := by
    let c10r21targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,5)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5),(2,5)]]
    let c10r21choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,6),(14,(0,0))),((1,7),(15,(0,0))),((2,1),(16,(0,0))),((2,5),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r21targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5)] c10r21choice = true := by decide
    refine ⟨c10r21targets, c10r21choice, ?_, checked⟩
    intro S h
    simp only [c10r21targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 12 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 25 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 11 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 23 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 13 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 27 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 21 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 22 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 28 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 12 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 18 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 20 _ (by rfl)))
  have c10r22_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6)] := by
    let c10r22targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,6)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6),(2,6)]]
    let c10r22choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,7),(15,(0,0))),((2,1),(16,(0,0))),((2,6),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r22targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6)] c10r22choice = true := by decide
    refine ⟨c10r22targets, c10r22choice, ?_, checked⟩
    intro S h
    simp only [c10r22targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 13 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 26 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 12 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 24 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 14 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 28 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 22 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 29 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 8 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 13 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 22 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 23 _ (by rfl)))
  have c10r23_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7)] := by
    let c10r23targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,7)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,7)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7),(2,7)]]
    let c10r23choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,8),(16,(0,0))),((2,1),(17,(0,0))),((2,7),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r23targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7)] c10r23choice = true := by decide
    refine ⟨c10r23targets, c10r23choice, ?_, checked⟩
    intro S h
    simp only [c10r23targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 14 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 27 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 13 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 25 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 15 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 29 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 23 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 18 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 21 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 26 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r16_closed
  · subst row; exact c10r17_closed
  · subst row; exact c10r18_closed
  · subst row; exact c10r19_closed
  · subst row; exact c10r20_closed
  · subst row; exact c10r21_closed
  · subst row; exact c10r22_closed
  · subst row; exact c10r23_closed
theorem C10R00000G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4)]]) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  have c10r24_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,1)] := by
    let c10r24targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(3,1)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(3,1)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(3,1)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(3,1)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(3,1)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,1),(3,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,4),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,5),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,6),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,7),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,0),(2,1)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,1),(3,1)]]
    let c10r24choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,2),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,0),(17,(0,0))),((2,2),(18,(0,0))),((3,1),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r24targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(2,1)] c10r24choice = true := by decide
    refine ⟨c10r24targets, c10r24choice, ?_, checked⟩
    intro S h
    simp only [c10r24targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 15 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 28 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 14 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 26 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 16 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 30 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 24 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 27 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 10 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 15 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 22 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 27 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 28 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 29 _ (by rfl)))
  have c10r25_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3)] := by
    let c10r25targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(2,3)]]
    let c10r25choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,4),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((1,7),(15,(0,0))),((2,2),(16,(0,0))),((2,3),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r25targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3)] c10r25choice = true := by decide
    refine ⟨c10r25targets, c10r25choice, ?_, checked⟩
    intro S h
    simp only [c10r25targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 16 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 29 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 15 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 27 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 17 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L56_lift _ (familyLookup_sound F11B063L56 [] 31 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 25 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 26 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 28 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 3 _ (by rfl)))
  have c10r26_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4)] := by
    let c10r26targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,4)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4),(2,4)]]
    let c10r26choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,3),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((1,7),(15,(0,0))),((2,2),(16,(0,0))),((2,4),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r26targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4)] c10r26choice = true := by decide
    refine ⟨c10r26targets, c10r26choice, ?_, checked⟩
    intro S h
    simp only [c10r26targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 17 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 30 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 16 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 28 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 18 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L57_lift _ (familyLookup_sound F11B063L57 [] 0 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 26 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 27 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 29 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 8 _ (by rfl)))
  have c10r27_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5)] := by
    let c10r27targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,5)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,5)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,5)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,5)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,5)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5),(2,5)]]
    let c10r27choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,6),(14,(0,0))),((1,7),(15,(0,0))),((2,2),(16,(0,0))),((2,5),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r27targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5)] c10r27choice = true := by decide
    refine ⟨c10r27targets, c10r27choice, ?_, checked⟩
    intro S h
    simp only [c10r27targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 18 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L21_lift _ (familyLookup_sound F11B029L21 [] 31 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 17 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 29 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 19 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L57_lift _ (familyLookup_sound F11B063L57 [] 1 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 27 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 28 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 10 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 11 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 12 _ (by rfl)))
  have c10r28_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6)] := by
    let c10r28targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,6)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,6)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,6)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,6)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,6)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6),(2,6)]]
    let c10r28choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,7),(15,(0,0))),((2,2),(16,(0,0))),((2,6),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r28targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6)] c10r28choice = true := by decide
    refine ⟨c10r28targets, c10r28choice, ?_, checked⟩
    intro S h
    simp only [c10r28targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 19 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L22_lift _ (familyLookup_sound F11B029L22 [] 0 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 18 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 30 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 20 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L57_lift _ (familyLookup_sound F11B063L57 [] 2 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 28 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 29 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L0_lift _ (familyLookup_sound F11B000L0 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 4 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 13 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 15 _ (by rfl)))
  have c10r29_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7)] := by
    let c10r29targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,7)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,7)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,7)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,7)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,7)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,7)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(2,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7),(1,8)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7),(2,7)]]
    let c10r29choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,8),(16,(0,0))),((2,2),(17,(0,0))),((2,7),(18,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r29targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7)] c10r29choice = true := by decide
    refine ⟨c10r29targets, c10r29choice, ?_, checked⟩
    intro S h
    simp only [c10r29targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 20 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L22_lift _ (familyLookup_sound F11B029L22 [] 1 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 19 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L5_lift _ (familyLookup_sound F11B053L5 [] 31 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 21 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L57_lift _ (familyLookup_sound F11B063L57 [] 3 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 29 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 1 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 10 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 13 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 16 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 18 _ (by rfl)))
  have c10r30_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(2,2)] := by
    let c10r30targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(3,2)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(3,2)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(3,2)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(3,2)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(3,2)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(3,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,4),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,5),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,6),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,7),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(2,1),(2,2)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(2,2),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(2,2),(3,2)]]
    let c10r30choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,3),(12,(0,0))),((1,4),(13,(0,0))),((1,5),(14,(0,0))),((1,6),(15,(0,0))),((1,7),(16,(0,0))),((2,1),(17,(0,0))),((2,3),(18,(0,0))),((3,2),(19,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r30targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(2,2)] c10r30choice = true := by decide
    refine ⟨c10r30targets, c10r30choice, ?_, checked⟩
    intro S h
    simp only [c10r30targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 21 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L22_lift _ (familyLookup_sound F11B029L22 [] 2 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 20 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L6_lift _ (familyLookup_sound F11B053L6 [] 0 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 22 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L57_lift _ (familyLookup_sound F11B063L57 [] 4 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 30 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L61_lift _ (familyLookup_sound F11B065L61 [] 31 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 8 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 5 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 2 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 7 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 11 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 14 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 17 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 19 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 20 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 21 _ (by rfl)))
  have c10r31_closed : FamilyRowClosed (fun S => FamilyMember S family11) [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4)] := by
    let c10r31targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,1),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(1,5)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(1,6)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(1,7)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(2,3)],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(2,4)]]
    let c10r31choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((-1,2),(2,(1,0))),((-1,3),(3,(1,0))),((-1,4),(4,(1,0))),((-1,5),(5,(1,0))),((-1,6),(6,(1,0))),((-1,7),(7,(1,0))),((0,-1),(8,(0,1))),((0,8),(9,(0,0))),((1,0),(10,(0,0))),((1,1),(11,(0,0))),((1,2),(12,(0,0))),((1,5),(13,(0,0))),((1,6),(14,(0,0))),((1,7),(15,(0,0))),((2,3),(16,(0,0))),((2,4),(17,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c10r31targets [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4)] c10r31choice = true := by decide
    refine ⟨c10r31targets, c10r31choice, ?_, checked⟩
    intro S h
    simp only [c10r31targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact F11B015_lift _ (F11B015L27_lift _ (familyLookup_sound F11B015L27 [] 22 _ (by rfl)))
    · subst S
      exact F11B029_lift _ (F11B029L22_lift _ (familyLookup_sound F11B029L22 [] 3 _ (by rfl)))
    · subst S
      exact F11B042_lift _ (F11B042L46_lift _ (familyLookup_sound F11B042L46 [] 21 _ (by rfl)))
    · subst S
      exact F11B053_lift _ (F11B053L6_lift _ (familyLookup_sound F11B053L6 [] 1 _ (by rfl)))
    · subst S
      exact F11B060_lift _ (F11B060L3_lift _ (familyLookup_sound F11B060L3 [] 23 _ (by rfl)))
    · subst S
      exact F11B063_lift _ (F11B063L57_lift _ (familyLookup_sound F11B063L57 [] 5 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L31_lift _ (familyLookup_sound F11B065L31 [] 31 _ (by rfl)))
    · subst S
      exact F11B065_lift _ (F11B065L62_lift _ (familyLookup_sound F11B065L62 [] 0 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 9 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L1_lift _ (familyLookup_sound F11B000L1 [] 3 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L2_lift _ (familyLookup_sound F11B000L2 [] 8 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 6 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L3_lift _ (familyLookup_sound F11B000L3 [] 30 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 22 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 23 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 24 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 25 _ (by rfl)))
    · subst S
      exact F11B000_lift _ (F11B000L4_lift _ (familyLookup_sound F11B000L4 [] 26 _ (by rfl)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c10r24_closed
  · subst row; exact c10r25_closed
  · subst row; exact c10r26_closed
  · subst row; exact c10r27_closed
  · subst row; exact c10r28_closed
  · subst row; exact c10r29_closed
  · subst row; exact c10r30_closed
  · subst row; exact c10r31_closed
theorem C10R00000_closed (row : List GridPoint) (h : FamilyMember row F10B000L0) : FamilyRowClosed (fun S => FamilyMember S family11) row := by
  simp only [F10B000L0, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C10R00000G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00000G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00000G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00000G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00000G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00000G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00000G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00000G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00000G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00000G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00000G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00000G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00000G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00000G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00000G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00000G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00000G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00000G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00000G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00000G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00000G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00000G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00000G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00000G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C10R00000G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C10R00000G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C10R00000G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C10R00000G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C10R00000G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C10R00000G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C10R00000G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C10R00000G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
