import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R05216G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5216_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r5216targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r5216choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5216targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0)] c9r5216choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5216targets, c9r5216choice, ?_, checked⟩
    intro S h
    simp only [c9r5216targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 19 _ (by rfl)
  have c9r5217_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r5217targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r5217choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5217targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1)] c9r5217choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5217targets, c9r5217choice, ?_, checked⟩
    intro S h
    simp only [c9r5217targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 21 _ (by rfl)
  have c9r5218_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r5218targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r5218choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5218targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,2)] c9r5218choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5218targets, c9r5218choice, ?_, checked⟩
    intro S h
    simp only [c9r5218targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 23 _ (by rfl)
  have c9r5219_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r5219targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r5219choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5219targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1)] c9r5219choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5219targets, c9r5219choice, ?_, checked⟩
    intro S h
    simp only [c9r5219targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 26 _ (by rfl)
  have c9r5220_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r5220targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r5220choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5220targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0)] c9r5220choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5220targets, c9r5220choice, ?_, checked⟩
    intro S h
    simp only [c9r5220targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 28 _ (by rfl)
  have c9r5221_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r5221targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r5221choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5221targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2)] c9r5221choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5221targets, c9r5221choice, ?_, checked⟩
    intro S h
    simp only [c9r5221targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 31 _ (by rfl)
  have c9r5222_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r5222targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r5222choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5222targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1),(5,1)] c9r5222choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5222targets, c9r5222choice, ?_, checked⟩
    intro S h
    simp only [c9r5222targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 2 _ (by rfl)
  have c9r5223_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)] := by
    let c9r5223targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(5,2)]]
    let c9r5223choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5223targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2)] c9r5223choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5223targets, c9r5223choice, ?_, checked⟩
    intro S h
    simp only [c9r5223targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 7 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5216_closed
  · subst row; exact c9r5217_closed
  · subst row; exact c9r5218_closed
  · subst row; exact c9r5219_closed
  · subst row; exact c9r5220_closed
  · subst row; exact c9r5221_closed
  · subst row; exact c9r5222_closed
  · subst row; exact c9r5223_closed
theorem C9R05216G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5224_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)] := by
    let c9r5224targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)]]
    let c9r5224choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5224targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0)] c9r5224choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5224targets, c9r5224choice, ?_, checked⟩
    intro S h
    simp only [c9r5224targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 9 _ (by rfl)
  have c9r5225_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)] := by
    let c9r5225targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1)]]
    let c9r5225choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5225targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,1)] c9r5225choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5225targets, c9r5225choice, ?_, checked⟩
    intro S h
    simp only [c9r5225targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 11 _ (by rfl)
  have c9r5226_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)] := by
    let c9r5226targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1),(6,1)]]
    let c9r5226choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5226targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1)] c9r5226choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5226targets, c9r5226choice, ?_, checked⟩
    intro S h
    simp only [c9r5226targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 14 _ (by rfl)
  have c9r5227_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)] := by
    let c9r5227targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0)]]
    let c9r5227choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r5227targets [(0,1),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0),(6,0)] c9r5227choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5227targets, c9r5227choice, ?_, checked⟩
    intro S h
    simp only [c9r5227targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 16 _ (by rfl)
  have c9r5228_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r5228targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(1,5),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r5228choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5228targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r5228choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5228targets, c9r5228choice, ?_, checked⟩
    intro S h
    simp only [c9r5228targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 22 _ (by rfl)
  have c9r5229_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c9r5229targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c9r5229choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5229targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1)] c9r5229choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5229targets, c9r5229choice, ?_, checked⟩
    intro S h
    simp only [c9r5229targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 27 _ (by rfl)
  have c9r5230_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r5230targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r5230choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5230targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2)] c9r5230choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5230targets, c9r5230choice, ?_, checked⟩
    intro S h
    simp only [c9r5230targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 30 _ (by rfl)
  have c9r5231_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r5231targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r5231choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5231targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3)] c9r5231choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5231targets, c9r5231choice, ?_, checked⟩
    intro S h
    simp only [c9r5231targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5224_closed
  · subst row; exact c9r5225_closed
  · subst row; exact c9r5226_closed
  · subst row; exact c9r5227_closed
  · subst row; exact c9r5228_closed
  · subst row; exact c9r5229_closed
  · subst row; exact c9r5230_closed
  · subst row; exact c9r5231_closed
theorem C9R05216G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5232_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r5232targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r5232choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5232targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r5232choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5232targets, c9r5232choice, ?_, checked⟩
    intro S h
    simp only [c9r5232targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 2 _ (by rfl)
  have c9r5233_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r5233targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r5233choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5233targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r5233choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5233targets, c9r5233choice, ?_, checked⟩
    intro S h
    simp only [c9r5233targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 6 _ (by rfl)
  have c9r5234_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)] := by
    let c9r5234targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)]]
    let c9r5234choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (8,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))))))
    have checked : successorFastRowCheck c9r5234targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2)] c9r5234choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5234targets, c9r5234choice, ?_, checked⟩
    intro S h
    simp only [c9r5234targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 9 _ (by rfl)
  have c9r5235_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)] := by
    let c9r5235targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)]]
    let c9r5235choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5235targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3)] c9r5235choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5235targets, c9r5235choice, ?_, checked⟩
    intro S h
    simp only [c9r5235targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 12 _ (by rfl)
  have c9r5236_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)] := by
    let c9r5236targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)]]
    let c9r5236choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5236targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1)] c9r5236choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5236targets, c9r5236choice, ?_, checked⟩
    intro S h
    simp only [c9r5236targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 15 _ (by rfl)
  have c9r5237_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)] := by
    let c9r5237targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)]]
    let c9r5237choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (8,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))))))
    have checked : successorFastRowCheck c9r5237targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3)] c9r5237choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5237targets, c9r5237choice, ?_, checked⟩
    intro S h
    simp only [c9r5237targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 18 _ (by rfl)
  have c9r5238_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)] := by
    let c9r5238targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)]]
    let c9r5238choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5238targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2)] c9r5238choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5238targets, c9r5238choice, ?_, checked⟩
    intro S h
    simp only [c9r5238targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 21 _ (by rfl)
  have c9r5239_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)] := by
    let c9r5239targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)]]
    let c9r5239choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5239targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4)] c9r5239choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5239targets, c9r5239choice, ?_, checked⟩
    intro S h
    simp only [c9r5239targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 24 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5232_closed
  · subst row; exact c9r5233_closed
  · subst row; exact c9r5234_closed
  · subst row; exact c9r5235_closed
  · subst row; exact c9r5236_closed
  · subst row; exact c9r5237_closed
  · subst row; exact c9r5238_closed
  · subst row; exact c9r5239_closed
theorem C9R05216G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5240_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)] := by
    let c9r5240targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)]]
    let c9r5240choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5240targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3)] c9r5240choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5240targets, c9r5240choice, ?_, checked⟩
    intro S h
    simp only [c9r5240targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 27 _ (by rfl)
  have c9r5241_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r5241targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r5241choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5241targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)] c9r5241choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5241targets, c9r5241choice, ?_, checked⟩
    intro S h
    simp only [c9r5241targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 0 _ (by rfl)
  have c9r5242_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c9r5242targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c9r5242choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5242targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)] c9r5242choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5242targets, c9r5242choice, ?_, checked⟩
    intro S h
    simp only [c9r5242targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 2 _ (by rfl)
  have c9r5243_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c9r5243targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c9r5243choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5243targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)] c9r5243choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5243targets, c9r5243choice, ?_, checked⟩
    intro S h
    simp only [c9r5243targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 4 _ (by rfl)
  have c9r5244_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)] := by
    let c9r5244targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)]]
    let c9r5244choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5244targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3)] c9r5244choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5244targets, c9r5244choice, ?_, checked⟩
    intro S h
    simp only [c9r5244targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 8 _ (by rfl)
  have c9r5245_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)] := by
    let c9r5245targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)]]
    let c9r5245choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5245targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1)] c9r5245choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5245targets, c9r5245choice, ?_, checked⟩
    intro S h
    simp only [c9r5245targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 11 _ (by rfl)
  have c9r5246_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)] := by
    let c9r5246targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c9r5246choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r5246targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,2)] c9r5246choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5246targets, c9r5246choice, ?_, checked⟩
    intro S h
    simp only [c9r5246targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 13 _ (by rfl)
  have c9r5247_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c9r5247targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c9r5247choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5247targets [(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)] c9r5247choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5247targets, c9r5247choice, ?_, checked⟩
    intro S h
    simp only [c9r5247targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5240_closed
  · subst row; exact c9r5241_closed
  · subst row; exact c9r5242_closed
  · subst row; exact c9r5243_closed
  · subst row; exact c9r5244_closed
  · subst row; exact c9r5245_closed
  · subst row; exact c9r5246_closed
  · subst row; exact c9r5247_closed
theorem C9R05216_closed (row : List GridPoint) (h : FamilyMember row F9B002L35) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L35, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R05216G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05216G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05216G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05216G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05216G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05216G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05216G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05216G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05216G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05216G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05216G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05216G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05216G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05216G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05216G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05216G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05216G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05216G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05216G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05216G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05216G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05216G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05216G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05216G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05216G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05216G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05216G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05216G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05216G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05216G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05216G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05216G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
