import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06048G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6048_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)] := by
    let c9r6048targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,0),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0),(6,0)]]
    let c9r6048choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6048targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0)] c9r6048choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6048targets, c9r6048choice, ?_, checked⟩
    intro S h
    simp only [c9r6048targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 2 _ (by rfl)
  have c9r6049_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)] := by
    let c9r6049targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2),(5,2)]]
    let c9r6049choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6049targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)] c9r6049choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6049targets, c9r6049choice, ?_, checked⟩
    intro S h
    simp only [c9r6049targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 5 _ (by rfl)
  have c9r6050_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)] := by
    let c9r6050targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3),(5,3)]]
    let c9r6050choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6050targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)] c9r6050choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6050targets, c9r6050choice, ?_, checked⟩
    intro S h
    simp only [c9r6050targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 8 _ (by rfl)
  have c9r6051_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)] := by
    let c9r6051targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2),(6,2)]]
    let c9r6051choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6051targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)] c9r6051choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6051targets, c9r6051choice, ?_, checked⟩
    intro S h
    simp only [c9r6051targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 11 _ (by rfl)
  have c9r6052_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)] := by
    let c9r6052targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6052choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6052targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2)] c9r6052choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6052targets, c9r6052choice, ?_, checked⟩
    intro S h
    simp only [c9r6052targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 15 _ (by rfl)
  have c9r6053_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)] := by
    let c9r6053targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0),(6,0)]]
    let c9r6053choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6053targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0)] c9r6053choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6053targets, c9r6053choice, ?_, checked⟩
    intro S h
    simp only [c9r6053targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 17 _ (by rfl)
  have c9r6054_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)] := by
    let c9r6054targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1),(6,1)]]
    let c9r6054choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6054targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,1)] c9r6054choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6054targets, c9r6054choice, ?_, checked⟩
    intro S h
    simp only [c9r6054targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 19 _ (by rfl)
  have c9r6055_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)] := by
    let c9r6055targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1),(6,1)]]
    let c9r6055choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6055targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1)] c9r6055choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6055targets, c9r6055choice, ?_, checked⟩
    intro S h
    simp only [c9r6055targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 22 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6048_closed
  · subst row; exact c9r6049_closed
  · subst row; exact c9r6050_closed
  · subst row; exact c9r6051_closed
  · subst row; exact c9r6052_closed
  · subst row; exact c9r6053_closed
  · subst row; exact c9r6054_closed
  · subst row; exact c9r6055_closed
theorem C9R06048G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6056_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)] := by
    let c9r6056targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0),(5,0),(6,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0),(7,0)]]
    let c9r6056choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6056targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0),(6,0)] c9r6056choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6056targets, c9r6056choice, ?_, checked⟩
    intro S h
    simp only [c9r6056targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 24 _ (by rfl)
  have c9r6057_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r6057targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r6057choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6057targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)] c9r6057choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6057targets, c9r6057choice, ?_, checked⟩
    intro S h
    simp only [c9r6057targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 29 _ (by rfl)
  have c9r6058_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r6058targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r6058choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6058targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1)] c9r6058choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6058targets, c9r6058choice, ?_, checked⟩
    intro S h
    simp only [c9r6058targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 1 _ (by rfl)
  have c9r6059_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r6059targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r6059choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6059targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)] c9r6059choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6059targets, c9r6059choice, ?_, checked⟩
    intro S h
    simp only [c9r6059targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 3 _ (by rfl)
  have c9r6060_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r6060targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r6060choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6060targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)] c9r6060choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6060targets, c9r6060choice, ?_, checked⟩
    intro S h
    simp only [c9r6060targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 5 _ (by rfl)
  have c9r6061_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r6061targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r6061choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6061targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] c9r6061choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6061targets, c9r6061choice, ?_, checked⟩
    intro S h
    simp only [c9r6061targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 8 _ (by rfl)
  have c9r6062_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r6062targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r6062choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6062targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)] c9r6062choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6062targets, c9r6062choice, ?_, checked⟩
    intro S h
    simp only [c9r6062targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 11 _ (by rfl)
  have c9r6063_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r6063targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r6063choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6063targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)] c9r6063choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6063targets, c9r6063choice, ?_, checked⟩
    intro S h
    simp only [c9r6063targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6056_closed
  · subst row; exact c9r6057_closed
  · subst row; exact c9r6058_closed
  · subst row; exact c9r6059_closed
  · subst row; exact c9r6060_closed
  · subst row; exact c9r6061_closed
  · subst row; exact c9r6062_closed
  · subst row; exact c9r6063_closed
theorem C9R06048G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6064_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r6064targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r6064choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6064targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)] c9r6064choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6064targets, c9r6064choice, ?_, checked⟩
    intro S h
    simp only [c9r6064targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 17 _ (by rfl)
  have c9r6065_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r6065targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r6065choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6065targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)] c9r6065choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6065targets, c9r6065choice, ?_, checked⟩
    intro S h
    simp only [c9r6065targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 20 _ (by rfl)
  have c9r6066_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r6066targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6066choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6066targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] c9r6066choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6066targets, c9r6066choice, ?_, checked⟩
    intro S h
    simp only [c9r6066targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 25 _ (by rfl)
  have c9r6067_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r6067targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r6067choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6067targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] c9r6067choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6067targets, c9r6067choice, ?_, checked⟩
    intro S h
    simp only [c9r6067targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 27 _ (by rfl)
  have c9r6068_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r6068targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r6068choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6068targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] c9r6068choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6068targets, c9r6068choice, ?_, checked⟩
    intro S h
    simp only [c9r6068targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 29 _ (by rfl)
  have c9r6069_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)] := by
    let c9r6069targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,3)]]
    let c9r6069choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6069targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)] c9r6069choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6069targets, c9r6069choice, ?_, checked⟩
    intro S h
    simp only [c9r6069targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 1 _ (by rfl)
  have c9r6070_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)] := by
    let c9r6070targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)]]
    let c9r6070choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6070targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)] c9r6070choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6070targets, c9r6070choice, ?_, checked⟩
    intro S h
    simp only [c9r6070targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 4 _ (by rfl)
  have c9r6071_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)] := by
    let c9r6071targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)]]
    let c9r6071choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6071targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)] c9r6071choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6071targets, c9r6071choice, ?_, checked⟩
    intro S h
    simp only [c9r6071targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6064_closed
  · subst row; exact c9r6065_closed
  · subst row; exact c9r6066_closed
  · subst row; exact c9r6067_closed
  · subst row; exact c9r6068_closed
  · subst row; exact c9r6069_closed
  · subst row; exact c9r6070_closed
  · subst row; exact c9r6071_closed
theorem C9R06048G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6072_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r6072targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r6072choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6072targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] c9r6072choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6072targets, c9r6072choice, ?_, checked⟩
    intro S h
    simp only [c9r6072targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 9 _ (by rfl)
  have c9r6073_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r6073targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r6073choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6073targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)] c9r6073choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6073targets, c9r6073choice, ?_, checked⟩
    intro S h
    simp only [c9r6073targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 12 _ (by rfl)
  have c9r6074_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r6074targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r6074choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6074targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)] c9r6074choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6074targets, c9r6074choice, ?_, checked⟩
    intro S h
    simp only [c9r6074targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 15 _ (by rfl)
  have c9r6075_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r6075targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,5),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r6075choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6075targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)] c9r6075choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6075targets, c9r6075choice, ?_, checked⟩
    intro S h
    simp only [c9r6075targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 20 _ (by rfl)
  have c9r6076_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r6076targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r6076choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6076targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)] c9r6076choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6076targets, c9r6076choice, ?_, checked⟩
    intro S h
    simp only [c9r6076targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 24 _ (by rfl)
  have c9r6077_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r6077targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r6077choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6077targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)] c9r6077choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6077targets, c9r6077choice, ?_, checked⟩
    intro S h
    simp only [c9r6077targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 26 _ (by rfl)
  have c9r6078_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)] := by
    let c9r6078targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)]]
    let c9r6078choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6078targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)] c9r6078choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6078targets, c9r6078choice, ?_, checked⟩
    intro S h
    simp only [c9r6078targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 28 _ (by rfl)
  have c9r6079_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)] := by
    let c9r6079targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,2),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)]]
    let c9r6079choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6079targets [(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)] c9r6079choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6079targets, c9r6079choice, ?_, checked⟩
    intro S h
    simp only [c9r6079targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,false,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6072_closed
  · subst row; exact c9r6073_closed
  · subst row; exact c9r6074_closed
  · subst row; exact c9r6075_closed
  · subst row; exact c9r6076_closed
  · subst row; exact c9r6077_closed
  · subst row; exact c9r6078_closed
  · subst row; exact c9r6079_closed
theorem C9R06048_closed (row : List GridPoint) (h : FamilyMember row F9B002L61) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L61, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06048G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06048G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06048G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06048G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06048G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06048G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06048G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06048G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06048G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06048G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06048G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06048G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06048G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06048G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06048G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06048G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06048G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06048G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06048G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06048G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06048G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06048G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06048G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06048G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06048G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06048G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06048G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06048G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06048G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06048G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06048G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06048G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
