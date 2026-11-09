import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R03744G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3744_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)] := by
    let c9r3744targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)]]
    let c9r3744choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3744targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)] c9r3744choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3744targets, c9r3744choice, ?_, checked⟩
    intro S h
    simp only [c9r3744targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 8 _ (by rfl)
  have c9r3745_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)] := by
    let c9r3745targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2),(6,2)]]
    let c9r3745choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3745targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2)] c9r3745choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3745targets, c9r3745choice, ?_, checked⟩
    intro S h
    simp only [c9r3745targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 13 _ (by rfl)
  have c9r3746_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)] := by
    let c9r3746targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0),(7,0)]]
    let c9r3746choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3746targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0)] c9r3746choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3746targets, c9r3746choice, ?_, checked⟩
    intro S h
    simp only [c9r3746targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 15 _ (by rfl)
  have c9r3747_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)] := by
    let c9r3747targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1),(7,1)]]
    let c9r3747choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3747targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,1)] c9r3747choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3747targets, c9r3747choice, ?_, checked⟩
    intro S h
    simp only [c9r3747targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 17 _ (by rfl)
  have c9r3748_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)] := by
    let c9r3748targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1),(7,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1),(7,1)]]
    let c9r3748choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3748targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1)] c9r3748choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3748targets, c9r3748choice, ?_, checked⟩
    intro S h
    simp only [c9r3748targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 20 _ (by rfl)
  have c9r3749_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)] := by
    let c9r3749targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,0),(6,0),(7,0),(8,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(5,1),(6,0),(7,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(6,1),(7,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0),(8,0)]]
    let c9r3749choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < -1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,1)) else (if b.1 < 8 ∨ (b.1 = 8 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3749targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(5,0),(6,0),(7,0)] c9r3749choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3749targets, c9r3749choice, ?_, checked⟩
    intro S h
    simp only [c9r3749targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 22 _ (by rfl)
  have c9r3750_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)] := by
    let c9r3750targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,4),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(5,4)]]
    let c9r3750choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3750targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)] c9r3750choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3750targets, c9r3750choice, ?_, checked⟩
    intro S h
    simp only [c9r3750targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 27 _ (by rfl)
  have c9r3751_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)] := by
    let c9r3751targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1),(6,1)]]
    let c9r3751choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3751targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)] c9r3751choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3751targets, c9r3751choice, ?_, checked⟩
    intro S h
    simp only [c9r3751targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3744_closed
  · subst row; exact c9r3745_closed
  · subst row; exact c9r3746_closed
  · subst row; exact c9r3747_closed
  · subst row; exact c9r3748_closed
  · subst row; exact c9r3749_closed
  · subst row; exact c9r3750_closed
  · subst row; exact c9r3751_closed
theorem C9R03744G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3752_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)] := by
    let c9r3752targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2),(6,2)]]
    let c9r3752choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3752targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)] c9r3752choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3752targets, c9r3752choice, ?_, checked⟩
    intro S h
    simp only [c9r3752targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
  have c9r3753_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)] := by
    let c9r3753targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(5,3),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3),(6,3)]]
    let c9r3753choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3753targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)] c9r3753choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3753targets, c9r3753choice, ?_, checked⟩
    intro S h
    simp only [c9r3753targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 3 _ (by rfl)
  have c9r3754_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r3754targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r3754choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3754targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)] c9r3754choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3754targets, c9r3754choice, ?_, checked⟩
    intro S h
    simp only [c9r3754targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 6 _ (by rfl)
  have c9r3755_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)] := by
    let c9r3755targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)]]
    let c9r3755choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3755targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)] c9r3755choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3755targets, c9r3755choice, ?_, checked⟩
    intro S h
    simp only [c9r3755targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 9 _ (by rfl)
  have c9r3756_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)] := by
    let c9r3756targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1),(7,1)]]
    let c9r3756choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3756targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)] c9r3756choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3756targets, c9r3756choice, ?_, checked⟩
    intro S h
    simp only [c9r3756targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 12 _ (by rfl)
  have c9r3757_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)] := by
    let c9r3757targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3),(5,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3),(6,3)]]
    let c9r3757choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3757targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)] c9r3757choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3757targets, c9r3757choice, ?_, checked⟩
    intro S h
    simp only [c9r3757targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 15 _ (by rfl)
  have c9r3758_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)] := by
    let c9r3758targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(5,2),(6,2),(7,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2),(6,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2),(7,2)]]
    let c9r3758choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3758targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)] c9r3758choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3758targets, c9r3758choice, ?_, checked⟩
    intro S h
    simp only [c9r3758targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 18 _ (by rfl)
  have c9r3759_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)] := by
    let c9r3759targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)]]
    let c9r3759choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3759targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)] c9r3759choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3759targets, c9r3759choice, ?_, checked⟩
    intro S h
    simp only [c9r3759targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3752_closed
  · subst row; exact c9r3753_closed
  · subst row; exact c9r3754_closed
  · subst row; exact c9r3755_closed
  · subst row; exact c9r3756_closed
  · subst row; exact c9r3757_closed
  · subst row; exact c9r3758_closed
  · subst row; exact c9r3759_closed
theorem C9R03744G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3760_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)] := by
    let c9r3760targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)]]
    let c9r3760choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3760targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)] c9r3760choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3760targets, c9r3760choice, ?_, checked⟩
    intro S h
    simp only [c9r3760targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 25 _ (by rfl)
  have c9r3761_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)] := by
    let c9r3761targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)]]
    let c9r3761choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3761targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)] c9r3761choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3761targets, c9r3761choice, ?_, checked⟩
    intro S h
    simp only [c9r3761targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 27 _ (by rfl)
  have c9r3762_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)] := by
    let c9r3762targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,3),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(5,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,3)]]
    let c9r3762choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3762targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)] c9r3762choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3762targets, c9r3762choice, ?_, checked⟩
    intro S h
    simp only [c9r3762targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 31 _ (by rfl)
  have c9r3763_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)] := by
    let c9r3763targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)]]
    let c9r3763choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3763targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)] c9r3763choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3763targets, c9r3763choice, ?_, checked⟩
    intro S h
    simp only [c9r3763targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 2 _ (by rfl)
  have c9r3764_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)] := by
    let c9r3764targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(6,2),(7,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2),(6,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2),(7,2)]]
    let c9r3764choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3764targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)] c9r3764choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3764targets, c9r3764choice, ?_, checked⟩
    intro S h
    simp only [c9r3764targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 4 _ (by rfl)
  have c9r3765_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)] := by
    let c9r3765targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)]]
    let c9r3765choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3765targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)] c9r3765choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3765targets, c9r3765choice, ?_, checked⟩
    intro S h
    simp only [c9r3765targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 7 _ (by rfl)
  have c9r3766_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)] := by
    let c9r3766targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(7,1),(7,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(7,2)]]
    let c9r3766choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3766targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)] c9r3766choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3766targets, c9r3766choice, ?_, checked⟩
    intro S h
    simp only [c9r3766targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 10 _ (by rfl)
  have c9r3767_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)] := by
    let c9r3767targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(5,1),(6,1),(7,1),(8,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1),(7,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1),(8,1)]]
    let c9r3767choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 8 ∨ (b.1 = 8 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3767targets [(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)] c9r3767choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3767targets, c9r3767choice, ?_, checked⟩
    intro S h
    simp only [c9r3767targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 13 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3760_closed
  · subst row; exact c9r3761_closed
  · subst row; exact c9r3762_closed
  · subst row; exact c9r3763_closed
  · subst row; exact c9r3764_closed
  · subst row; exact c9r3765_closed
  · subst row; exact c9r3766_closed
  · subst row; exact c9r3767_closed
theorem C9R03744G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3768_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r3768targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(3,4),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(3,4),(4,1),(4,2),(4,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,3),(3,4),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(3,4),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r3768choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3768targets [(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r3768choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3768targets, c9r3768choice, ?_, checked⟩
    intro S h
    simp only [c9r3768targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 18 _ (by rfl)
  have c9r3769_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r3769targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r3769choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3769targets [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)] c9r3769choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3769targets, c9r3769choice, ?_, checked⟩
    intro S h
    simp only [c9r3769targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 23 _ (by rfl)
  have c9r3770_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r3770targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r3770choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3770targets [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)] c9r3770choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3770targets, c9r3770choice, ?_, checked⟩
    intro S h
    simp only [c9r3770targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 26 _ (by rfl)
  have c9r3771_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r3771targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r3771choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3771targets [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)] c9r3771choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3771targets, c9r3771choice, ?_, checked⟩
    intro S h
    simp only [c9r3771targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 28 _ (by rfl)
  have c9r3772_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r3772targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r3772choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3772targets [(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)] c9r3772choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3772targets, c9r3772choice, ?_, checked⟩
    intro S h
    simp only [c9r3772targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 30 _ (by rfl)
  have c9r3773_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r3773targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,4),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,4),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,4),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,3),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,4),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(3,0),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r3773choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3773targets [(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)] c9r3773choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3773targets, c9r3773choice, ?_, checked⟩
    intro S h
    simp only [c9r3773targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 5 _ (by rfl)
  have c9r3774_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)] := by
    let c9r3774targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(3,0),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,4)]]
    let c9r3774choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (12,(0,1)) else (13,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (16,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (17,(0,0)) else (18,(0,0)))))))
    have checked : successorFastRowCheck c9r3774targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4)] c9r3774choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3774targets, c9r3774choice, ?_, checked⟩
    intro S h
    simp only [c9r3774targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 12 _ (by rfl)
  have c9r3775_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)] := by
    let c9r3775targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(5,1),(5,2),(5,3),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(0,1),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(1,0),(1,1),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(1,0),(2,0),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(1,0),(2,0),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0),(5,3)],[(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0),(6,0)]]
    let c9r3775choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3775targets [(0,0),(1,0),(2,0),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0)] c9r3775choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3775targets, c9r3775choice, ?_, checked⟩
    intro S h
    simp only [c9r3775targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,false,false,false,false] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3768_closed
  · subst row; exact c9r3769_closed
  · subst row; exact c9r3770_closed
  · subst row; exact c9r3771_closed
  · subst row; exact c9r3772_closed
  · subst row; exact c9r3773_closed
  · subst row; exact c9r3774_closed
  · subst row; exact c9r3775_closed
theorem C9R03744_closed (row : List GridPoint) (h : FamilyMember row F9B001L53) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L53, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R03744G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03744G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03744G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03744G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03744G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03744G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03744G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03744G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03744G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03744G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03744G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03744G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03744G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03744G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03744G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03744G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03744G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03744G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03744G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03744G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03744G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03744G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03744G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03744G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03744G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03744G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03744G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03744G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03744G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03744G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03744G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03744G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
