import Lean
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R02176G0 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2176_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)] := by
    let c9r2176targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,4),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,4),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(2,5),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)]]
    let c9r2176choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((1,4),(6,(0,0))),((2,0),(7,(0,0))),((2,3),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,5),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2176targets [(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)] c9r2176choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2176targets, c9r2176choice, ?_, checked⟩
    intro S h
    simp only [c9r2176targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 12 _ (by rfl)
  have c9r2177_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r2177targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r2177choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2177targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r2177choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2177targets, c9r2177choice, ?_, checked⟩
    intro S h
    simp only [c9r2177targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 18 _ (by rfl)
  have c9r2178_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r2178targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r2178choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((5,0),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2178targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r2178choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2178targets, c9r2178choice, ?_, checked⟩
    intro S h
    simp only [c9r2178targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 21 _ (by rfl)
  have c9r2179_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r2179targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r2179choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,1),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2179targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r2179choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2179targets, c9r2179choice, ?_, checked⟩
    intro S h
    simp only [c9r2179targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 23 _ (by rfl)
  have c9r2180_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r2180targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r2180choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2180targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r2180choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2180targets, c9r2180choice, ?_, checked⟩
    intro S h
    simp only [c9r2180targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 25 _ (by rfl)
  have c9r2181_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r2181targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r2181choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2181targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] c9r2181choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2181targets, c9r2181choice, ?_, checked⟩
    intro S h
    simp only [c9r2181targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 28 _ (by rfl)
  have c9r2182_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r2182targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r2182choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,1),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2182targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] c9r2182choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2182targets, c9r2182choice, ?_, checked⟩
    intro S h
    simp only [c9r2182targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 30 _ (by rfl)
  have c9r2183_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r2183targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r2183choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2183targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] c9r2183choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2183targets, c9r2183choice, ?_, checked⟩
    intro S h
    simp only [c9r2183targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2176_closed
  · subst row; exact c9r2177_closed
  · subst row; exact c9r2178_closed
  · subst row; exact c9r2179_closed
  · subst row; exact c9r2180_closed
  · subst row; exact c9r2181_closed
  · subst row; exact c9r2182_closed
  · subst row; exact c9r2183_closed
theorem C9R02176G1 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2184_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r2184targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r2184choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,-1),(8,(0,1))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2184targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] c9r2184choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2184targets, c9r2184choice, ?_, checked⟩
    intro S h
    simp only [c9r2184targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 4 _ (by rfl)
  have c9r2185_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r2185targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r2185choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,0),(9,(0,0))),((3,5),(10,(0,0))),((4,1),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2185targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)] c9r2185choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2185targets, c9r2185choice, ?_, checked⟩
    intro S h
    simp only [c9r2185targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 10 _ (by rfl)
  have c9r2186_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r2186targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r2186choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2186targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)] c9r2186choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2186targets, c9r2186choice, ?_, checked⟩
    intro S h
    simp only [c9r2186targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 14 _ (by rfl)
  have c9r2187_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r2187targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r2187choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,2),(12,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2187targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)] c9r2187choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2187targets, c9r2187choice, ?_, checked⟩
    intro S h
    simp only [c9r2187targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 16 _ (by rfl)
  have c9r2188_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r2188targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r2188choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,4),(9,(0,0))),((4,1),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2188targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)] c9r2188choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2188targets, c9r2188choice, ?_, checked⟩
    intro S h
    simp only [c9r2188targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 18 _ (by rfl)
  have c9r2189_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r2189targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r2189choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2189targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] c9r2189choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2189targets, c9r2189choice, ?_, checked⟩
    intro S h
    simp only [c9r2189targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 21 _ (by rfl)
  have c9r2190_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r2190targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r2190choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2190targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)] c9r2190choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2190targets, c9r2190choice, ?_, checked⟩
    intro S h
    simp only [c9r2190targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 24 _ (by rfl)
  have c9r2191_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r2191targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r2191choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2191targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)] c9r2191choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2191targets, c9r2191choice, ?_, checked⟩
    intro S h
    simp only [c9r2191targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2184_closed
  · subst row; exact c9r2185_closed
  · subst row; exact c9r2186_closed
  · subst row; exact c9r2187_closed
  · subst row; exact c9r2188_closed
  · subst row; exact c9r2189_closed
  · subst row; exact c9r2190_closed
  · subst row; exact c9r2191_closed
theorem C9R02176G2 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2192_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r2192targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r2192choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,4),(11,(0,0))),((5,2),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2192targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)] c9r2192choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2192targets, c9r2192choice, ?_, checked⟩
    intro S h
    simp only [c9r2192targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 30 _ (by rfl)
  have c9r2193_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r2193targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r2193choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,3),(9,(0,0))),((4,1),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2193targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)] c9r2193choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2193targets, c9r2193choice, ?_, checked⟩
    intro S h
    simp only [c9r2193targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 1 _ (by rfl)
  have c9r2194_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r2194targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r2194choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2194targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] c9r2194choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2194targets, c9r2194choice, ?_, checked⟩
    intro S h
    simp only [c9r2194targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 6 _ (by rfl)
  have c9r2195_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r2195targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r2195choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,1),(13,(0,0))),((6,0),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2195targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] c9r2195choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2195targets, c9r2195choice, ?_, checked⟩
    intro S h
    simp only [c9r2195targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 8 _ (by rfl)
  have c9r2196_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r2196targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r2196choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,-1),(10,(0,1))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2196targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] c9r2196choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2196targets, c9r2196choice, ?_, checked⟩
    intro S h
    simp only [c9r2196targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 10 _ (by rfl)
  have c9r2197_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r2197targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r2197choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((3,3),(10,(0,0))),((4,0),(11,(0,0))),((4,4),(12,(0,0))),((5,1),(13,(0,0))),((5,2),(14,(0,0))),((5,3),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2197targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)] c9r2197choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2197targets, c9r2197choice, ?_, checked⟩
    intro S h
    simp only [c9r2197targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 14 _ (by rfl)
  have c9r2198_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r2198targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r2198choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,1),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2198targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)] c9r2198choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2198targets, c9r2198choice, ?_, checked⟩
    intro S h
    simp only [c9r2198targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 17 _ (by rfl)
  have c9r2199_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r2199targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r2199choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,3),(13,(0,0))),((6,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2199targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)] c9r2199choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2199targets, c9r2199choice, ?_, checked⟩
    intro S h
    simp only [c9r2199targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2192_closed
  · subst row; exact c9r2193_closed
  · subst row; exact c9r2194_closed
  · subst row; exact c9r2195_closed
  · subst row; exact c9r2196_closed
  · subst row; exact c9r2197_closed
  · subst row; exact c9r2198_closed
  · subst row; exact c9r2199_closed
theorem C9R02176G3 (row : List GridPoint) (h : row ∈ [[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r2200_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r2200targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r2200choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,-1),(12,(0,1))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,1),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2200targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] c9r2200choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2200targets, c9r2200choice, ?_, checked⟩
    intro S h
    simp only [c9r2200targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 22 _ (by rfl)
  have c9r2201_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r2201targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r2201choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,3),(13,(0,0))),((6,1),(14,(0,0))),((6,2),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2201targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)] c9r2201choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2201targets, c9r2201choice, ?_, checked⟩
    intro S h
    simp only [c9r2201targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 25 _ (by rfl)
  have c9r2202_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r2202targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r2202choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,0),(8,(0,0))),((3,2),(9,(0,0))),((4,0),(10,(0,0))),((4,2),(11,(0,0))),((5,0),(12,(0,0))),((5,2),(13,(0,0))),((6,0),(14,(0,0))),((6,2),(15,(0,0))),((7,1),(16,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2202targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)] c9r2202choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2202targets, c9r2202choice, ?_, checked⟩
    intro S h
    simp only [c9r2202targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 28 _ (by rfl)
  have c9r2203_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r2203targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r2203choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((2,5),(9,(0,0))),((3,1),(10,(0,0))),((3,6),(11,(0,0))),((4,2),(12,(0,0))),((4,3),(13,(0,0))),((4,4),(14,(0,0))),((4,5),(15,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2203targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)] c9r2203choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2203targets, c9r2203choice, ?_, checked⟩
    intro S h
    simp only [c9r2203targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 1 _ (by rfl)
  have c9r2204_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r2204targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r2204choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,1),(11,(0,0))),((4,3),(12,(0,0))),((4,4),(13,(0,0))),((5,2),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2204targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)] c9r2204choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2204targets, c9r2204choice, ?_, checked⟩
    intro S h
    simp only [c9r2204targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 5 _ (by rfl)
  have c9r2205_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r2205targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r2205choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,2),(11,(0,0))),((4,4),(12,(0,0))),((5,3),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2205targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)] c9r2205choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2205targets, c9r2205choice, ?_, checked⟩
    intro S h
    simp only [c9r2205targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 7 _ (by rfl)
  have c9r2206_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r2206targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r2206choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((2,4),(8,(0,0))),((3,1),(9,(0,0))),((3,5),(10,(0,0))),((4,2),(11,(0,0))),((4,3),(12,(0,0))),((4,5),(13,(0,0))),((5,4),(14,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2206targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)] c9r2206choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2206targets, c9r2206choice, ?_, checked⟩
    intro S h
    simp only [c9r2206targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 9 _ (by rfl)
  have c9r2207_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)] := by
    let c9r2207targets : Array (List GridPoint) := #[[(0,0),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(0,2),(1,2),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)]]
    let c9r2207choice (b : GridPoint) : ℕ × GridPoint := (([((-1,0),(0,(1,0))),((-1,1),(1,(1,0))),((0,-1),(2,(0,1))),((0,2),(3,(0,0))),((1,0),(4,(0,0))),((1,2),(5,(0,0))),((2,0),(6,(0,0))),((2,3),(7,(0,0))),((3,1),(8,(0,0))),((3,4),(9,(0,0))),((4,0),(10,(0,0))),((4,3),(11,(0,0))),((5,1),(12,(0,0))),((5,2),(13,(0,0)))] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))
    have checked : successorFastRowCheck c9r2207targets [(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)] c9r2207choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r2207targets, c9r2207choice, ?_, checked⟩
    intro S h
    simp only [c9r2207targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r2200_closed
  · subst row; exact c9r2201_closed
  · subst row; exact c9r2202_closed
  · subst row; exact c9r2203_closed
  · subst row; exact c9r2204_closed
  · subst row; exact c9r2205_closed
  · subst row; exact c9r2206_closed
  · subst row; exact c9r2207_closed
theorem C9R02176_closed (row : List GridPoint) (h : FamilyMember row F9B001L4) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L4, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R02176G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02176G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02176G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02176G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02176G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02176G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02176G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02176G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02176G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02176G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02176G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02176G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02176G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02176G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02176G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02176G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02176G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02176G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02176G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02176G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02176G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02176G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02176G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02176G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R02176G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R02176G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R02176G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R02176G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R02176G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R02176G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R02176G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R02176G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
