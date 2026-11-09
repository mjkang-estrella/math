import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R08256G0 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8256_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)] := by
    let c9r8256targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(4,4),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(6,0)]]
    let c9r8256choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8256targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)] c9r8256choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8256targets, c9r8256choice, ?_, checked⟩
    intro S h
    simp only [c9r8256targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 31 _ (by rfl)
  have c9r8257_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)] := by
    let c9r8257targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(6,1)]]
    let c9r8257choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8257targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)] c9r8257choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8257targets, c9r8257choice, ?_, checked⟩
    intro S h
    simp only [c9r8257targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 2 _ (by rfl)
  have c9r8258_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)] := by
    let c9r8258targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2),(6,2)]]
    let c9r8258choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8258targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)] c9r8258choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8258targets, c9r8258choice, ?_, checked⟩
    intro S h
    simp only [c9r8258targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 4 _ (by rfl)
  have c9r8259_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)] := by
    let c9r8259targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,3)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(5,4)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3),(6,3)]]
    let c9r8259choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8259targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)] c9r8259choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8259targets, c9r8259choice, ?_, checked⟩
    intro S h
    simp only [c9r8259targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 6 _ (by rfl)
  have c9r8260_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r8260targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r8260choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8260targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)] c9r8260choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8260targets, c9r8260choice, ?_, checked⟩
    intro S h
    simp only [c9r8260targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 9 _ (by rfl)
  have c9r8261_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)] := by
    let c9r8261targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2),(6,2)]]
    let c9r8261choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8261targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)] c9r8261choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8261targets, c9r8261choice, ?_, checked⟩
    intro S h
    simp only [c9r8261targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 12 _ (by rfl)
  have c9r8262_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)] := by
    let c9r8262targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0),(7,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(6,0)],[(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2),(6,0)],[(0,3),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0),(7,0)]]
    let c9r8262choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8262targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)] c9r8262choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8262targets, c9r8262choice, ?_, checked⟩
    intro S h
    simp only [c9r8262targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 14 _ (by rfl)
  have c9r8263_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)] := by
    let c9r8263targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(6,2)]]
    let c9r8263choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8263targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)] c9r8263choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8263targets, c9r8263choice, ?_, checked⟩
    intro S h
    simp only [c9r8263targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8256_closed
  · subst row; exact c9r8257_closed
  · subst row; exact c9r8258_closed
  · subst row; exact c9r8259_closed
  · subst row; exact c9r8260_closed
  · subst row; exact c9r8261_closed
  · subst row; exact c9r8262_closed
  · subst row; exact c9r8263_closed
theorem C9R08256G1 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8264_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)] := by
    let c9r8264targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1),(7,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1),(7,1)]]
    let c9r8264choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8264targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)] c9r8264choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8264targets, c9r8264choice, ?_, checked⟩
    intro S h
    simp only [c9r8264targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 20 _ (by rfl)
  have c9r8265_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)] := by
    let c9r8265targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2),(6,3)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(5,4)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(6,3)]]
    let c9r8265choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8265targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)] c9r8265choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8265targets, c9r8265choice, ?_, checked⟩
    intro S h
    simp only [c9r8265targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 23 _ (by rfl)
  have c9r8266_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)] := by
    let c9r8266targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2),(7,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3),(6,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2),(6,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2),(7,2)]]
    let c9r8266choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8266targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)] c9r8266choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8266targets, c9r8266choice, ?_, checked⟩
    intro S h
    simp only [c9r8266targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 26 _ (by rfl)
  have c9r8267_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r8267targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,2),(6,0),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,3),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,3),(4,1),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r8267choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8267targets [(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)] c9r8267choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8267targets, c9r8267choice, ?_, checked⟩
    intro S h
    simp only [c9r8267targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 31 _ (by rfl)
  have c9r8268_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)] := by
    let c9r8268targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3),(6,0),(6,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4),(5,0),(5,1)],[(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(4,4),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(6,1)]]
    let c9r8268choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8268targets [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)] c9r8268choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8268targets, c9r8268choice, ?_, checked⟩
    intro S h
    simp only [c9r8268targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 4 _ (by rfl)
  have c9r8269_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r8269targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r8269choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8269targets [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)] c9r8269choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8269targets, c9r8269choice, ?_, checked⟩
    intro S h
    simp only [c9r8269targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 9 _ (by rfl)
  have c9r8270_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)] := by
    let c9r8270targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1),(7,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(6,0)],[(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0),(7,0)]]
    let c9r8270choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8270targets [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)] c9r8270choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8270targets, c9r8270choice, ?_, checked⟩
    intro S h
    simp only [c9r8270targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 11 _ (by rfl)
  have c9r8271_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)] := by
    let c9r8271targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1),(7,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(6,1)],[(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1),(7,1)]]
    let c9r8271choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8271targets [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)] c9r8271choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8271targets, c9r8271choice, ?_, checked⟩
    intro S h
    simp only [c9r8271targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8264_closed
  · subst row; exact c9r8265_closed
  · subst row; exact c9r8266_closed
  · subst row; exact c9r8267_closed
  · subst row; exact c9r8268_closed
  · subst row; exact c9r8269_closed
  · subst row; exact c9r8270_closed
  · subst row; exact c9r8271_closed
theorem C9R08256G2 (row : List GridPoint) (h : row ∈ [[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8272_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)] := by
    let c9r8272targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,1),(7,0),(7,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,3),(1,3),(2,3),(3,3),(4,2),(4,3),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1),(7,1)]]
    let c9r8272choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8272targets [(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)] c9r8272choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8272targets, c9r8272choice, ?_, checked⟩
    intro S h
    simp only [c9r8272targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 17 _ (by rfl)
  have c9r8273_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)] := by
    let c9r8273targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3),(6,0),(6,1),(6,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(4,4),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,3),(3,3),(4,3),(4,4),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,2)]]
    let c9r8273choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8273targets [(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)] c9r8273choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8273targets, c9r8273choice, ?_, checked⟩
    intro S h
    simp only [c9r8273targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 24 _ (by rfl)
  have c9r8274_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)] := by
    let c9r8274targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2),(6,3)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,3),(1,3),(2,3),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3),(5,4)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(5,4)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,3)]]
    let c9r8274choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8274targets [(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)] c9r8274choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8274targets, c9r8274choice, ?_, checked⟩
    intro S h
    simp only [c9r8274targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 31 _ (by rfl)
  have c9r8275_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)] := by
    let c9r8275targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2),(7,0)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,0)],[(0,3),(1,3),(2,3),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,0)],[(0,3),(1,3),(2,3),(3,3),(4,3),(5,1),(5,2),(5,3),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0),(7,0)]]
    let c9r8275choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (13,(0,0)) else (14,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8275targets [(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)] c9r8275choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8275targets, c9r8275choice, ?_, checked⟩
    intro S h
    simp only [c9r8275targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 2 _ (by rfl)
  have c9r8276_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)] := by
    let c9r8276targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2),(7,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,1)],[(0,3),(1,3),(2,3),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1),(7,1)]]
    let c9r8276choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8276targets [(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)] c9r8276choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8276targets, c9r8276choice, ?_, checked⟩
    intro S h
    simp only [c9r8276targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 4 _ (by rfl)
  have c9r8277_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)] := by
    let c9r8277targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2),(7,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2),(6,2)],[(0,3),(1,3),(2,3),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3),(6,3)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2),(6,3)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2),(7,2)]]
    let c9r8277choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8277targets [(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)] c9r8277choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8277targets, c9r8277choice, ?_, checked⟩
    intro S h
    simp only [c9r8277targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 6 _ (by rfl)
  have c9r8278_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)] := by
    let c9r8278targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,1),(6,2),(7,0),(7,1)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3),(6,0),(6,1)],[(0,3),(1,3),(2,3),(3,3),(4,3),(5,2),(5,3),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1),(7,1)]]
    let c9r8278choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8278targets [(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)] c9r8278choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8278targets, c9r8278choice, ?_, checked⟩
    intro S h
    simp only [c9r8278targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 11 _ (by rfl)
  have c9r8279_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)] := by
    let c9r8279targets : Array (List GridPoint) := #[[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,2),(7,0),(7,1),(7,2)],[(0,1),(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,1),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(4,3),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,0),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(5,3),(6,0),(6,1),(6,2)],[(0,3),(1,3),(2,3),(3,3),(4,3),(5,3),(6,0),(6,1),(6,2),(6,3)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2),(6,3)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2),(7,0)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2),(7,1)],[(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2),(7,2)]]
    let c9r8279choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,1)) else (15,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (16,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c9r8279targets [(0,2),(1,2),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)] c9r8279choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8279targets, c9r8279choice, ?_, checked⟩
    intro S h
    simp only [c9r8279targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8272_closed
  · subst row; exact c9r8273_closed
  · subst row; exact c9r8274_closed
  · subst row; exact c9r8275_closed
  · subst row; exact c9r8276_closed
  · subst row; exact c9r8277_closed
  · subst row; exact c9r8278_closed
  · subst row; exact c9r8279_closed
theorem C9R08256G3 (row : List GridPoint) (h : row ∈ [[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r8280_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3)] := by
    let c9r8280targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3)],[(0,4),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3)],[(0,5),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3)],[(0,6),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3)],[(0,7),(1,3),(1,4),(1,5),(1,6),(1,7),(2,0),(2,1),(2,2),(2,3)],[(0,0),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3)],[(0,1),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3)],[(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3)],[(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,2),(1,3)],[(0,4),(0,5),(0,6),(0,7),(0,8),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,6)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,7)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(2,3)]]
    let c9r8280choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 7) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (4,(1,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (6,(0,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 8) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r8280targets [(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3)] c9r8280choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8280targets, c9r8280choice, ?_, checked⟩
    intro S h
    simp only [c9r8280targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 28 _ (by rfl)
  have c9r8281_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)] := by
    let c9r8281targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,0),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4)],[(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)]]
    let c9r8281choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8281targets [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4)] c9r8281choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8281targets, c9r8281choice, ?_, checked⟩
    intro S h
    simp only [c9r8281targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 6 _ (by rfl)
  have c9r8282_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5)] := by
    let c9r8282targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,0),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,5)],[(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,5)]]
    let c9r8282choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8282targets [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5)] c9r8282choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8282targets, c9r8282choice, ?_, checked⟩
    intro S h
    simp only [c9r8282targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 12 _ (by rfl)
  have c9r8283_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6)] := by
    let c9r8283targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,6)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,6)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,6)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,6)],[(0,0),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,6)],[(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(1,7)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,6)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(1,6)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(1,7)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(2,0)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(2,6)]]
    let c9r8283choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 7) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8283targets [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6)] c9r8283choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8283targets, c9r8283choice, ?_, checked⟩
    intro S h
    simp only [c9r8283targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 18 _ (by rfl)
  have c9r8284_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0)] := by
    let c9r8284targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,0),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(2,0)],[(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,0)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(2,0)],[(0,4),(0,5),(0,6),(0,7),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)]]
    let c9r8284choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8284targets [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0)] c9r8284choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8284targets, c9r8284choice, ?_, checked⟩
    intro S h
    simp only [c9r8284targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 22 _ (by rfl)
  have c9r8285_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1)] := by
    let c9r8285targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,0),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(2,1)],[(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)]]
    let c9r8285choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8285targets [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1)] c9r8285choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8285targets, c9r8285choice, ?_, checked⟩
    intro S h
    simp only [c9r8285targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 25 _ (by rfl)
  have c9r8286_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2)] := by
    let c9r8286targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,0),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(2,2)],[(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)]]
    let c9r8286choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r8286targets [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2)] c9r8286choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8286targets, c9r8286choice, ?_, checked⟩
    intro S h
    simp only [c9r8286targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 27 _ (by rfl)
  have c9r8287_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3)] := by
    let c9r8287targets : Array (List GridPoint) := #[[(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,4),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,5),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,6),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,0),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,1),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,3),(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(2,3)],[(0,4),(0,5),(0,6),(0,7),(1,0),(1,1),(1,2),(1,3),(1,4),(2,4)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,5),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,6),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,0),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4)],[(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3)]]
    let c9r8287choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 5) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (0,(1,0)) else (1,(1,0))) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 6) then (2,(1,0)) else (3,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 7) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r8287targets [(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(2,3)] c9r8287choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r8287targets, c9r8287choice, ?_, checked⟩
    intro S h
    simp only [c9r8287targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,false,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,false,false] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r8280_closed
  · subst row; exact c9r8281_closed
  · subst row; exact c9r8282_closed
  · subst row; exact c9r8283_closed
  · subst row; exact c9r8284_closed
  · subst row; exact c9r8285_closed
  · subst row; exact c9r8286_closed
  · subst row; exact c9r8287_closed
theorem C9R08256_closed (row : List GridPoint) (h : FamilyMember row F9B004L2) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L2, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R08256G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08256G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08256G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08256G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08256G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08256G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08256G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08256G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08256G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08256G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08256G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08256G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08256G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08256G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08256G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08256G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08256G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08256G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08256G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08256G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08256G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08256G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08256G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08256G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R08256G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R08256G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R08256G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R08256G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R08256G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R08256G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R08256G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R08256G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
