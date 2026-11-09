import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R04416G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4416_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r4416targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r4416choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4416targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] c9r4416choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4416targets, c9r4416choice, ?_, checked⟩
    intro S h
    simp only [c9r4416targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 13 _ (by rfl)
  have c9r4417_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r4417targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r4417choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4417targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] c9r4417choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4417targets, c9r4417choice, ?_, checked⟩
    intro S h
    simp only [c9r4417targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 15 _ (by rfl)
  have c9r4418_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r4418targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r4418choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4418targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3)] c9r4418choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4418targets, c9r4418choice, ?_, checked⟩
    intro S h
    simp only [c9r4418targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 19 _ (by rfl)
  have c9r4419_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r4419targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r4419choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4419targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1)] c9r4419choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4419targets, c9r4419choice, ?_, checked⟩
    intro S h
    simp only [c9r4419targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 22 _ (by rfl)
  have c9r4420_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r4420targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r4420choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4420targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2)] c9r4420choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4420targets, c9r4420choice, ?_, checked⟩
    intro S h
    simp only [c9r4420targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 24 _ (by rfl)
  have c9r4421_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r4421targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r4421choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4421targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] c9r4421choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4421targets, c9r4421choice, ?_, checked⟩
    intro S h
    simp only [c9r4421targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 27 _ (by rfl)
  have c9r4422_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r4422targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r4422choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4422targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2)] c9r4422choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4422targets, c9r4422choice, ?_, checked⟩
    intro S h
    simp only [c9r4422targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 30 _ (by rfl)
  have c9r4423_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r4423targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r4423choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,1)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4423targets [(0,1),(0,2),(1,0),(1,1),(2,1),(3,1),(4,1),(5,1),(6,1)] c9r4423choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4423targets, c9r4423choice, ?_, checked⟩
    intro S h
    simp only [c9r4423targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4416_closed
  · subst row; exact c9r4417_closed
  · subst row; exact c9r4418_closed
  · subst row; exact c9r4419_closed
  · subst row; exact c9r4420_closed
  · subst row; exact c9r4421_closed
  · subst row; exact c9r4422_closed
  · subst row; exact c9r4423_closed
theorem C9R04416G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4424_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c9r4424targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c9r4424choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4424targets [(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c9r4424choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4424targets, c9r4424choice, ?_, checked⟩
    intro S h
    simp only [c9r4424targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 7 _ (by rfl)
  have c9r4425_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r4425targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r4425choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4425targets [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r4425choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4425targets, c9r4425choice, ?_, checked⟩
    intro S h
    simp only [c9r4425targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 12 _ (by rfl)
  have c9r4426_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r4426targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r4426choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4426targets [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c9r4426choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4426targets, c9r4426choice, ?_, checked⟩
    intro S h
    simp only [c9r4426targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 15 _ (by rfl)
  have c9r4427_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r4427targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r4427choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r4427targets [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)] c9r4427choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4427targets, c9r4427choice, ?_, checked⟩
    intro S h
    simp only [c9r4427targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 17 _ (by rfl)
  have c9r4428_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r4428targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r4428choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4428targets [(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)] c9r4428choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4428targets, c9r4428choice, ?_, checked⟩
    intro S h
    simp only [c9r4428targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 19 _ (by rfl)
  have c9r4429_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r4429targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r4429choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4429targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r4429choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4429targets, c9r4429choice, ?_, checked⟩
    intro S h
    simp only [c9r4429targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 27 _ (by rfl)
  have c9r4430_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r4430targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r4430choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4430targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r4430choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4430targets, c9r4430choice, ?_, checked⟩
    intro S h
    simp only [c9r4430targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 31 _ (by rfl)
  have c9r4431_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r4431targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r4431choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4431targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r4431choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4431targets, c9r4431choice, ?_, checked⟩
    intro S h
    simp only [c9r4431targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4424_closed
  · subst row; exact c9r4425_closed
  · subst row; exact c9r4426_closed
  · subst row; exact c9r4427_closed
  · subst row; exact c9r4428_closed
  · subst row; exact c9r4429_closed
  · subst row; exact c9r4430_closed
  · subst row; exact c9r4431_closed
theorem C9R04416G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4432_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r4432targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r4432choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4432targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r4432choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4432targets, c9r4432choice, ?_, checked⟩
    intro S h
    simp only [c9r4432targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 4 _ (by rfl)
  have c9r4433_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r4433targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r4433choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4433targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r4433choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4433targets, c9r4433choice, ?_, checked⟩
    intro S h
    simp only [c9r4433targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 6 _ (by rfl)
  have c9r4434_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] := by
    let c9r4434targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)]]
    let c9r4434choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4434targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)] c9r4434choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4434targets, c9r4434choice, ?_, checked⟩
    intro S h
    simp only [c9r4434targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 9 _ (by rfl)
  have c9r4435_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] := by
    let c9r4435targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)]]
    let c9r4435choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4435targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)] c9r4435choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4435targets, c9r4435choice, ?_, checked⟩
    intro S h
    simp only [c9r4435targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 12 _ (by rfl)
  have c9r4436_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] := by
    let c9r4436targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)],[(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)]]
    let c9r4436choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4436targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)] c9r4436choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4436targets, c9r4436choice, ?_, checked⟩
    intro S h
    simp only [c9r4436targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 14 _ (by rfl)
  have c9r4437_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] := by
    let c9r4437targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)]]
    let c9r4437choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,1)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4437targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)] c9r4437choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4437targets, c9r4437choice, ?_, checked⟩
    intro S h
    simp only [c9r4437targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 17 _ (by rfl)
  have c9r4438_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] := by
    let c9r4438targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)]]
    let c9r4438choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4438targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)] c9r4438choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4438targets, c9r4438choice, ?_, checked⟩
    intro S h
    simp only [c9r4438targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 20 _ (by rfl)
  have c9r4439_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] := by
    let c9r4439targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)]]
    let c9r4439choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4439targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)] c9r4439choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4439targets, c9r4439choice, ?_, checked⟩
    intro S h
    simp only [c9r4439targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4432_closed
  · subst row; exact c9r4433_closed
  · subst row; exact c9r4434_closed
  · subst row; exact c9r4435_closed
  · subst row; exact c9r4436_closed
  · subst row; exact c9r4437_closed
  · subst row; exact c9r4438_closed
  · subst row; exact c9r4439_closed
theorem C9R04416G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4440_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] := by
    let c9r4440targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)]]
    let c9r4440choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4440targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)] c9r4440choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4440targets, c9r4440choice, ?_, checked⟩
    intro S h
    simp only [c9r4440targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 26 _ (by rfl)
  have c9r4441_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r4441targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,0),(1,1),(1,3),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r4441choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (3,(0,0)) else (4,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4441targets [(0,1),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2)] c9r4441choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4441targets, c9r4441choice, ?_, checked⟩
    intro S h
    simp only [c9r4441targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,false,true] 31 _ (by rfl)
  have c9r4442_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] := by
    let c9r4442targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)]]
    let c9r4442choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4442targets [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)] c9r4442choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4442targets, c9r4442choice, ?_, checked⟩
    intro S h
    simp only [c9r4442targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 6 _ (by rfl)
  have c9r4443_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c9r4443targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c9r4443choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4443targets [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c9r4443choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4443targets, c9r4443choice, ?_, checked⟩
    intro S h
    simp only [c9r4443targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 12 _ (by rfl)
  have c9r4444_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] := by
    let c9r4444targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,3)]]
    let c9r4444choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4444targets [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)] c9r4444choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4444targets, c9r4444choice, ?_, checked⟩
    intro S h
    simp only [c9r4444targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 16 _ (by rfl)
  have c9r4445_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] := by
    let c9r4445targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,5)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(2,5)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,4)]]
    let c9r4445choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4445targets [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)] c9r4445choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4445targets, c9r4445choice, ?_, checked⟩
    intro S h
    simp only [c9r4445targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 20 _ (by rfl)
  have c9r4446_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] := by
    let c9r4446targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,0)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,0)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,0)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(4,0)]]
    let c9r4446choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4446targets [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)] c9r4446choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4446targets, c9r4446choice, ?_, checked⟩
    intro S h
    simp only [c9r4446targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 22 _ (by rfl)
  have c9r4447_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] := by
    let c9r4447targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1),(4,1)]]
    let c9r4447choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4447targets [(0,1),(0,2),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)] c9r4447choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4447targets, c9r4447choice, ?_, checked⟩
    intro S h
    simp only [c9r4447targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,true,true,false,true,false] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4440_closed
  · subst row; exact c9r4441_closed
  · subst row; exact c9r4442_closed
  · subst row; exact c9r4443_closed
  · subst row; exact c9r4444_closed
  · subst row; exact c9r4445_closed
  · subst row; exact c9r4446_closed
  · subst row; exact c9r4447_closed
theorem C9R04416_closed (row : List GridPoint) (h : FamilyMember row F9B002L10) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L10, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R04416G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04416G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04416G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04416G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04416G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04416G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04416G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04416G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04416G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04416G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04416G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04416G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04416G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04416G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04416G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04416G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04416G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04416G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04416G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04416G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04416G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04416G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04416G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04416G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04416G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04416G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04416G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04416G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04416G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04416G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04416G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04416G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
