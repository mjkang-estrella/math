import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R04192G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4192_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r4192targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r4192choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4192targets [(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r4192choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4192targets, c9r4192choice, ?_, checked⟩
    intro S h
    simp only [c9r4192targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 9 _ (by rfl)
  have c9r4193_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r4193targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r4193choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4193targets [(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r4193choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4193targets, c9r4193choice, ?_, checked⟩
    intro S h
    simp only [c9r4193targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 11 _ (by rfl)
  have c9r4194_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r4194targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r4194choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4194targets [(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r4194choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4194targets, c9r4194choice, ?_, checked⟩
    intro S h
    simp only [c9r4194targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 13 _ (by rfl)
  have c9r4195_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r4195targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r4195choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4195targets [(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r4195choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4195targets, c9r4195choice, ?_, checked⟩
    intro S h
    simp only [c9r4195targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 21 _ (by rfl)
  have c9r4196_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r4196targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r4196choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4196targets [(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r4196choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4196targets, c9r4196choice, ?_, checked⟩
    intro S h
    simp only [c9r4196targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 28 _ (by rfl)
  have c9r4197_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r4197targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r4197choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r4197targets [(0,1),(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r4197choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4197targets, c9r4197choice, ?_, checked⟩
    intro S h
    simp only [c9r4197targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 4 _ (by rfl)
  have c9r4198_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c9r4198targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,5),(1,1),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,2),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c9r4198choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (3,(1,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4198targets [(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4)] c9r4198choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4198targets, c9r4198choice, ?_, checked⟩
    intro S h
    simp only [c9r4198targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 14 _ (by rfl)
  have c9r4199_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c9r4199targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c9r4199choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4199targets [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c9r4199choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4199targets, c9r4199choice, ?_, checked⟩
    intro S h
    simp only [c9r4199targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4192_closed
  · subst row; exact c9r4193_closed
  · subst row; exact c9r4194_closed
  · subst row; exact c9r4195_closed
  · subst row; exact c9r4196_closed
  · subst row; exact c9r4197_closed
  · subst row; exact c9r4198_closed
  · subst row; exact c9r4199_closed
theorem C9R04192G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4200_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] := by
    let c9r4200targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,3),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)]]
    let c9r4200choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4200targets [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)] c9r4200choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4200targets, c9r4200choice, ?_, checked⟩
    intro S h
    simp only [c9r4200targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 28 _ (by rfl)
  have c9r4201_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] := by
    let c9r4201targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]
    let c9r4201choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4201targets [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)] c9r4201choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4201targets, c9r4201choice, ?_, checked⟩
    intro S h
    simp only [c9r4201targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 0 _ (by rfl)
  have c9r4202_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] := by
    let c9r4202targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(3,2)]]
    let c9r4202choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4202targets [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)] c9r4202choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4202targets, c9r4202choice, ?_, checked⟩
    intro S h
    simp only [c9r4202targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 3 _ (by rfl)
  have c9r4203_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] := by
    let c9r4203targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(3,3)]]
    let c9r4203choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (6,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4203targets [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)] c9r4203choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4203targets, c9r4203choice, ?_, checked⟩
    intro S h
    simp only [c9r4203targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 5 _ (by rfl)
  have c9r4204_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] := by
    let c9r4204targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,4),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,0),(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(2,5)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4),(3,4)]]
    let c9r4204choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4204targets [(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)] c9r4204choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4204targets, c9r4204choice, ?_, checked⟩
    intro S h
    simp only [c9r4204targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 7 _ (by rfl)
  have c9r4205_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c9r4205targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,3),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c9r4205choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4205targets [(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c9r4205choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4205targets, c9r4205choice, ?_, checked⟩
    intro S h
    simp only [c9r4205targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 17 _ (by rfl)
  have c9r4206_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c9r4206targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c9r4206choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4206targets [(0,1),(0,2),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c9r4206choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4206targets, c9r4206choice, ?_, checked⟩
    intro S h
    simp only [c9r4206targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 26 _ (by rfl)
  have c9r4207_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] := by
    let c9r4207targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(1,1),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,5),(1,1),(1,2),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,0),(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,3),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,1),(0,2),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,2),(0,3),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)]]
    let c9r4207choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4207targets [(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)] c9r4207choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4207targets, c9r4207choice, ?_, checked⟩
    intro S h
    simp only [c9r4207targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4200_closed
  · subst row; exact c9r4201_closed
  · subst row; exact c9r4202_closed
  · subst row; exact c9r4203_closed
  · subst row; exact c9r4204_closed
  · subst row; exact c9r4205_closed
  · subst row; exact c9r4206_closed
  · subst row; exact c9r4207_closed
theorem C9R04192G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4208_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] := by
    let c9r4208targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,1),(0,2),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)]]
    let c9r4208choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4208targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6)] c9r4208choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4208targets, c9r4208choice, ?_, checked⟩
    intro S h
    simp only [c9r4208targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 16 _ (by rfl)
  have c9r4209_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] := by
    let c9r4209targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)]]
    let c9r4209choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4209targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0)] c9r4209choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4209targets, c9r4209choice, ?_, checked⟩
    intro S h
    simp only [c9r4209targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 22 _ (by rfl)
  have c9r4210_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] := by
    let c9r4210targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)]]
    let c9r4210choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4210targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1)] c9r4210choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4210targets, c9r4210choice, ?_, checked⟩
    intro S h
    simp only [c9r4210targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 27 _ (by rfl)
  have c9r4211_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] := by
    let c9r4211targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)]]
    let c9r4211choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4211targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2)] c9r4211choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4211targets, c9r4211choice, ?_, checked⟩
    intro S h
    simp only [c9r4211targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 31 _ (by rfl)
  have c9r4212_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] := by
    let c9r4212targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(3,3)]]
    let c9r4212choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4212targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3)] c9r4212choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4212targets, c9r4212choice, ?_, checked⟩
    intro S h
    simp only [c9r4212targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 2 _ (by rfl)
  have c9r4213_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] := by
    let c9r4213targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(3,4)]]
    let c9r4213choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4213targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4)] c9r4213choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4213targets, c9r4213choice, ?_, checked⟩
    intro S h
    simp only [c9r4213targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 4 _ (by rfl)
  have c9r4214_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] := by
    let c9r4214targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,1),(0,2),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(2,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5),(3,5)]]
    let c9r4214choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4214targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,5)] c9r4214choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4214targets, c9r4214choice, ?_, checked⟩
    intro S h
    simp only [c9r4214targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 6 _ (by rfl)
  have c9r4215_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c9r4215targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c9r4215choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4215targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c9r4215choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4215targets, c9r4215choice, ?_, checked⟩
    intro S h
    simp only [c9r4215targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4208_closed
  · subst row; exact c9r4209_closed
  · subst row; exact c9r4210_closed
  · subst row; exact c9r4211_closed
  · subst row; exact c9r4212_closed
  · subst row; exact c9r4213_closed
  · subst row; exact c9r4214_closed
  · subst row; exact c9r4215_closed
theorem C9R04192G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4216_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)] := by
    let c9r4216targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,2)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,2)]]
    let c9r4216choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4216targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2)] c9r4216choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4216targets, c9r4216choice, ?_, checked⟩
    intro S h
    simp only [c9r4216targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 15 _ (by rfl)
  have c9r4217_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)] := by
    let c9r4217targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,3)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,3)]]
    let c9r4217choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4217targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3)] c9r4217choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4217targets, c9r4217choice, ?_, checked⟩
    intro S h
    simp only [c9r4217targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 18 _ (by rfl)
  have c9r4218_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)] := by
    let c9r4218targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,4)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,4)]]
    let c9r4218choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4218targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4)] c9r4218choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4218targets, c9r4218choice, ?_, checked⟩
    intro S h
    simp only [c9r4218targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 21 _ (by rfl)
  have c9r4219_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)] := by
    let c9r4219targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,4),(3,0)],[(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0),(4,0)]]
    let c9r4219choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4219targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(3,0)] c9r4219choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4219targets, c9r4219choice, ?_, checked⟩
    intro S h
    simp only [c9r4219targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 23 _ (by rfl)
  have c9r4220_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)] := by
    let c9r4220targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,2)]]
    let c9r4220choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r4220targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2)] c9r4220choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4220targets, c9r4220choice, ?_, checked⟩
    intro S h
    simp only [c9r4220targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 27 _ (by rfl)
  have c9r4221_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)] := by
    let c9r4221targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,3)]]
    let c9r4221choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r4221targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3)] c9r4221choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4221targets, c9r4221choice, ?_, checked⟩
    intro S h
    simp only [c9r4221targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 30 _ (by rfl)
  have c9r4222_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)] := by
    let c9r4222targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(2,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(2,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,4)]]
    let c9r4222choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r4222targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4)] c9r4222choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4222targets, c9r4222choice, ?_, checked⟩
    intro S h
    simp only [c9r4222targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 1 _ (by rfl)
  have c9r4223_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)] := by
    let c9r4223targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,2),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)],[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,1),(0,2),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)],[(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,3),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(2,4),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1),(4,1)]]
    let c9r4223choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4223targets [(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1),(3,1)] c9r4223choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4223targets, c9r4223choice, ?_, checked⟩
    intro S h
    simp only [c9r4223targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,false,true,false,false] 4 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4216_closed
  · subst row; exact c9r4217_closed
  · subst row; exact c9r4218_closed
  · subst row; exact c9r4219_closed
  · subst row; exact c9r4220_closed
  · subst row; exact c9r4221_closed
  · subst row; exact c9r4222_closed
  · subst row; exact c9r4223_closed
theorem C9R04192_closed (row : List GridPoint) (h : FamilyMember row F9B002L3) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L3, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R04192G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04192G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04192G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04192G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04192G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04192G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04192G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04192G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04192G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04192G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04192G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04192G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04192G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04192G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04192G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04192G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04192G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04192G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04192G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04192G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04192G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04192G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04192G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04192G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04192G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04192G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04192G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04192G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04192G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04192G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04192G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04192G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
