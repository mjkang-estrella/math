import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R05536G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5536_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r5536targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r5536choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5536targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r5536choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5536targets, c9r5536choice, ?_, checked⟩
    intro S h
    simp only [c9r5536targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 24 _ (by rfl)
  have c9r5537_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r5537targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r5537choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5537targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r5537choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5537targets, c9r5537choice, ?_, checked⟩
    intro S h
    simp only [c9r5537targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 26 _ (by rfl)
  have c9r5538_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r5538targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r5538choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5538targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] c9r5538choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5538targets, c9r5538choice, ?_, checked⟩
    intro S h
    simp only [c9r5538targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 29 _ (by rfl)
  have c9r5539_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r5539targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r5539choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5539targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] c9r5539choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5539targets, c9r5539choice, ?_, checked⟩
    intro S h
    simp only [c9r5539targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 31 _ (by rfl)
  have c9r5540_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r5540targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r5540choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5540targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] c9r5540choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5540targets, c9r5540choice, ?_, checked⟩
    intro S h
    simp only [c9r5540targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 2 _ (by rfl)
  have c9r5541_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r5541targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r5541choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5541targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] c9r5541choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5541targets, c9r5541choice, ?_, checked⟩
    intro S h
    simp only [c9r5541targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 5 _ (by rfl)
  have c9r5542_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r5542targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r5542choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5542targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)] c9r5542choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5542targets, c9r5542choice, ?_, checked⟩
    intro S h
    simp only [c9r5542targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 11 _ (by rfl)
  have c9r5543_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r5543targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r5543choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5543targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)] c9r5543choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5543targets, c9r5543choice, ?_, checked⟩
    intro S h
    simp only [c9r5543targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5536_closed
  · subst row; exact c9r5537_closed
  · subst row; exact c9r5538_closed
  · subst row; exact c9r5539_closed
  · subst row; exact c9r5540_closed
  · subst row; exact c9r5541_closed
  · subst row; exact c9r5542_closed
  · subst row; exact c9r5543_closed
theorem C9R05536G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5544_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r5544targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r5544choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5544targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)] c9r5544choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5544targets, c9r5544choice, ?_, checked⟩
    intro S h
    simp only [c9r5544targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 17 _ (by rfl)
  have c9r5545_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r5545targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r5545choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5545targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)] c9r5545choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5545targets, c9r5545choice, ?_, checked⟩
    intro S h
    simp only [c9r5545targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 19 _ (by rfl)
  have c9r5546_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r5546targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r5546choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5546targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] c9r5546choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5546targets, c9r5546choice, ?_, checked⟩
    intro S h
    simp only [c9r5546targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 22 _ (by rfl)
  have c9r5547_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r5547targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r5547choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5547targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)] c9r5547choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5547targets, c9r5547choice, ?_, checked⟩
    intro S h
    simp only [c9r5547targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 25 _ (by rfl)
  have c9r5548_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r5548targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r5548choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5548targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)] c9r5548choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5548targets, c9r5548choice, ?_, checked⟩
    intro S h
    simp only [c9r5548targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 28 _ (by rfl)
  have c9r5549_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r5549targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r5549choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5549targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)] c9r5549choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5549targets, c9r5549choice, ?_, checked⟩
    intro S h
    simp only [c9r5549targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 31 _ (by rfl)
  have c9r5550_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r5550targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r5550choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5550targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)] c9r5550choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5550targets, c9r5550choice, ?_, checked⟩
    intro S h
    simp only [c9r5550targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 2 _ (by rfl)
  have c9r5551_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r5551targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r5551choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5551targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] c9r5551choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5551targets, c9r5551choice, ?_, checked⟩
    intro S h
    simp only [c9r5551targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 7 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5544_closed
  · subst row; exact c9r5545_closed
  · subst row; exact c9r5546_closed
  · subst row; exact c9r5547_closed
  · subst row; exact c9r5548_closed
  · subst row; exact c9r5549_closed
  · subst row; exact c9r5550_closed
  · subst row; exact c9r5551_closed
theorem C9R05536G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5552_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r5552targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r5552choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5552targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] c9r5552choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5552targets, c9r5552choice, ?_, checked⟩
    intro S h
    simp only [c9r5552targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 9 _ (by rfl)
  have c9r5553_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r5553targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r5553choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5553targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] c9r5553choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5553targets, c9r5553choice, ?_, checked⟩
    intro S h
    simp only [c9r5553targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 11 _ (by rfl)
  have c9r5554_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r5554targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r5554choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5554targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)] c9r5554choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5554targets, c9r5554choice, ?_, checked⟩
    intro S h
    simp only [c9r5554targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 15 _ (by rfl)
  have c9r5555_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r5555targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r5555choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5555targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)] c9r5555choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5555targets, c9r5555choice, ?_, checked⟩
    intro S h
    simp only [c9r5555targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 18 _ (by rfl)
  have c9r5556_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r5556targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r5556choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5556targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)] c9r5556choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5556targets, c9r5556choice, ?_, checked⟩
    intro S h
    simp only [c9r5556targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 20 _ (by rfl)
  have c9r5557_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r5557targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r5557choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5557targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] c9r5557choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5557targets, c9r5557choice, ?_, checked⟩
    intro S h
    simp only [c9r5557targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 23 _ (by rfl)
  have c9r5558_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r5558targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r5558choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5558targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)] c9r5558choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5558targets, c9r5558choice, ?_, checked⟩
    intro S h
    simp only [c9r5558targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 26 _ (by rfl)
  have c9r5559_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r5559targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r5559choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5559targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)] c9r5559choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5559targets, c9r5559choice, ?_, checked⟩
    intro S h
    simp only [c9r5559targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5552_closed
  · subst row; exact c9r5553_closed
  · subst row; exact c9r5554_closed
  · subst row; exact c9r5555_closed
  · subst row; exact c9r5556_closed
  · subst row; exact c9r5557_closed
  · subst row; exact c9r5558_closed
  · subst row; exact c9r5559_closed
theorem C9R05536G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5560_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r5560targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r5560choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5560targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)] c9r5560choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5560targets, c9r5560choice, ?_, checked⟩
    intro S h
    simp only [c9r5560targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 2 _ (by rfl)
  have c9r5561_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r5561targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r5561choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5561targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)] c9r5561choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5561targets, c9r5561choice, ?_, checked⟩
    intro S h
    simp only [c9r5561targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 6 _ (by rfl)
  have c9r5562_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r5562targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r5562choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5562targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)] c9r5562choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5562targets, c9r5562choice, ?_, checked⟩
    intro S h
    simp only [c9r5562targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 8 _ (by rfl)
  have c9r5563_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r5563targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r5563choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5563targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)] c9r5563choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5563targets, c9r5563choice, ?_, checked⟩
    intro S h
    simp only [c9r5563targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 10 _ (by rfl)
  have c9r5564_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)] := by
    let c9r5564targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)]]
    let c9r5564choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5564targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)] c9r5564choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5564targets, c9r5564choice, ?_, checked⟩
    intro S h
    simp only [c9r5564targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 14 _ (by rfl)
  have c9r5565_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)] := by
    let c9r5565targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)]]
    let c9r5565choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5565targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)] c9r5565choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5565targets, c9r5565choice, ?_, checked⟩
    intro S h
    simp only [c9r5565targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 17 _ (by rfl)
  have c9r5566_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)] := by
    let c9r5566targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(6,2)]]
    let c9r5566choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5566targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)] c9r5566choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5566targets, c9r5566choice, ?_, checked⟩
    intro S h
    simp only [c9r5566targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 20 _ (by rfl)
  have c9r5567_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)] := by
    let c9r5567targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,4)]]
    let c9r5567choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5567targets [(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)] c9r5567choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5567targets, c9r5567choice, ?_, checked⟩
    intro S h
    simp only [c9r5567targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,false] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5560_closed
  · subst row; exact c9r5561_closed
  · subst row; exact c9r5562_closed
  · subst row; exact c9r5563_closed
  · subst row; exact c9r5564_closed
  · subst row; exact c9r5565_closed
  · subst row; exact c9r5566_closed
  · subst row; exact c9r5567_closed
theorem C9R05536_closed (row : List GridPoint) (h : FamilyMember row F9B002L45) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L45, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R05536G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05536G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05536G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05536G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05536G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05536G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05536G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05536G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05536G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05536G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05536G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05536G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05536G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05536G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05536G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05536G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05536G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05536G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05536G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05536G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05536G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05536G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05536G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05536G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05536G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05536G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05536G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05536G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05536G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05536G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05536G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05536G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
