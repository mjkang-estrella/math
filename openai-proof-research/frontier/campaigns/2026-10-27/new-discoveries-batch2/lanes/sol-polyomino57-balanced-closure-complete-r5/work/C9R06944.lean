import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06944G0 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6944_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r6944targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r6944choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6944targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r6944choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6944targets, c9r6944choice, ?_, checked⟩
    intro S h
    simp only [c9r6944targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 29 _ (by rfl)
  have c9r6945_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r6945targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6945choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6945targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)] c9r6945choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6945targets, c9r6945choice, ?_, checked⟩
    intro S h
    simp only [c9r6945targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 2 _ (by rfl)
  have c9r6946_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r6946targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r6946choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6946targets [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r6946choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6946targets, c9r6946choice, ?_, checked⟩
    intro S h
    simp only [c9r6946targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 7 _ (by rfl)
  have c9r6947_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r6947targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6947choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6947targets [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)] c9r6947choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6947targets, c9r6947choice, ?_, checked⟩
    intro S h
    simp only [c9r6947targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 12 _ (by rfl)
  have c9r6948_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)] := by
    let c9r6948targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]
    let c9r6948choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6948targets [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)] c9r6948choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6948targets, c9r6948choice, ?_, checked⟩
    intro S h
    simp only [c9r6948targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 14 _ (by rfl)
  have c9r6949_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)] := by
    let c9r6949targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)]]
    let c9r6949choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6949targets [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)] c9r6949choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6949targets, c9r6949choice, ?_, checked⟩
    intro S h
    simp only [c9r6949targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 16 _ (by rfl)
  have c9r6950_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)] := by
    let c9r6950targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(0,4),(1,3),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)]]
    let c9r6950choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6950targets [(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)] c9r6950choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6950targets, c9r6950choice, ?_, checked⟩
    intro S h
    simp only [c9r6950targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 20 _ (by rfl)
  have c9r6951_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r6951targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6951choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6951targets [(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r6951choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6951targets, c9r6951choice, ?_, checked⟩
    intro S h
    simp only [c9r6951targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6944_closed
  · subst row; exact c9r6945_closed
  · subst row; exact c9r6946_closed
  · subst row; exact c9r6947_closed
  · subst row; exact c9r6948_closed
  · subst row; exact c9r6949_closed
  · subst row; exact c9r6950_closed
  · subst row; exact c9r6951_closed
theorem C9R06944G1 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6952_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r6952targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(0,4),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r6952choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6952targets [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)] c9r6952choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6952targets, c9r6952choice, ?_, checked⟩
    intro S h
    simp only [c9r6952targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 2 _ (by rfl)
  have c9r6953_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r6953targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,3),(0,4),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(0,4),(1,3),(2,3),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r6953choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6953targets [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)] c9r6953choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6953targets, c9r6953choice, ?_, checked⟩
    intro S h
    simp only [c9r6953targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 5 _ (by rfl)
  have c9r6954_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r6954targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(0,4),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r6954choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6954targets [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)] c9r6954choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6954targets, c9r6954choice, ?_, checked⟩
    intro S h
    simp only [c9r6954targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 7 _ (by rfl)
  have c9r6955_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r6955targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,3),(0,4),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r6955choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6955targets [(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)] c9r6955choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6955targets, c9r6955choice, ?_, checked⟩
    intro S h
    simp only [c9r6955targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 9 _ (by rfl)
  have c9r6956_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r6956targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(0,4),(1,3),(2,3),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r6956choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6956targets [(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)] c9r6956choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6956targets, c9r6956choice, ?_, checked⟩
    intro S h
    simp only [c9r6956targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 14 _ (by rfl)
  have c9r6957_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r6957targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(0,4),(1,3),(2,3),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r6957choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,1)) else (14,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r6957targets [(0,2),(0,3),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)] c9r6957choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6957targets, c9r6957choice, ?_, checked⟩
    intro S h
    simp only [c9r6957targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 20 _ (by rfl)
  have c9r6958_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r6958targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,5),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,0),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,1),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,5)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r6958choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6958targets [(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)] c9r6958choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6958targets, c9r6958choice, ?_, checked⟩
    intro S h
    simp only [c9r6958targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 29 _ (by rfl)
  have c9r6959_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] := by
    let c9r6959targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,3),(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)]]
    let c9r6959choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6959targets [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] c9r6959choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6959targets, c9r6959choice, ?_, checked⟩
    intro S h
    simp only [c9r6959targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6952_closed
  · subst row; exact c9r6953_closed
  · subst row; exact c9r6954_closed
  · subst row; exact c9r6955_closed
  · subst row; exact c9r6956_closed
  · subst row; exact c9r6957_closed
  · subst row; exact c9r6958_closed
  · subst row; exact c9r6959_closed
theorem C9R06944G2 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6960_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)] := by
    let c9r6960targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,4),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(4,0)]]
    let c9r6960choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6960targets [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0)] c9r6960choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6960targets, c9r6960choice, ?_, checked⟩
    intro S h
    simp only [c9r6960targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 10 _ (by rfl)
  have c9r6961_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)] := by
    let c9r6961targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,3),(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1)]]
    let c9r6961choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6961targets [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)] c9r6961choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6961targets, c9r6961choice, ?_, checked⟩
    intro S h
    simp only [c9r6961targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 13 _ (by rfl)
  have c9r6962_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)] := by
    let c9r6962targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,3),(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2)]]
    let c9r6962choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6962targets [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2)] c9r6962choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6962targets, c9r6962choice, ?_, checked⟩
    intro S h
    simp only [c9r6962targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 15 _ (by rfl)
  have c9r6963_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)] := by
    let c9r6963targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,3),(0,4),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3)]]
    let c9r6963choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6963targets [(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3)] c9r6963choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6963targets, c9r6963choice, ?_, checked⟩
    intro S h
    simp only [c9r6963targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 17 _ (by rfl)
  have c9r6964_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r6964targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,4),(1,5),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r6964choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6964targets [(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r6964choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6964targets, c9r6964choice, ?_, checked⟩
    intro S h
    simp only [c9r6964targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 25 _ (by rfl)
  have c9r6965_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r6965targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,4),(1,5),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r6965choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6965targets [(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r6965choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6965targets, c9r6965choice, ?_, checked⟩
    intro S h
    simp only [c9r6965targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 0 _ (by rfl)
  have c9r6966_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r6966targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(1,5),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,4),(1,5),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r6966choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6966targets [(0,2),(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r6966choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6966targets, c9r6966choice, ?_, checked⟩
    intro S h
    simp only [c9r6966targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 8 _ (by rfl)
  have c9r6967_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] := by
    let c9r6967targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)]]
    let c9r6967choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6967targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5)] c9r6967choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6967targets, c9r6967choice, ?_, checked⟩
    intro S h
    simp only [c9r6967targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6960_closed
  · subst row; exact c9r6961_closed
  · subst row; exact c9r6962_closed
  · subst row; exact c9r6963_closed
  · subst row; exact c9r6964_closed
  · subst row; exact c9r6965_closed
  · subst row; exact c9r6966_closed
  · subst row; exact c9r6967_closed
theorem C9R06944G3 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6968_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] := by
    let c9r6968targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0)],[(0,3),(0,4),(1,4),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(4,0)]]
    let c9r6968choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6968targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0)] c9r6968choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6968targets, c9r6968choice, ?_, checked⟩
    intro S h
    simp only [c9r6968targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 25 _ (by rfl)
  have c9r6969_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] := by
    let c9r6969targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(4,1)]]
    let c9r6969choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6969targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1)] c9r6969choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6969targets, c9r6969choice, ?_, checked⟩
    intro S h
    simp only [c9r6969targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 29 _ (by rfl)
  have c9r6970_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] := by
    let c9r6970targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)]]
    let c9r6970choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6970targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2)] c9r6970choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6970targets, c9r6970choice, ?_, checked⟩
    intro S h
    simp only [c9r6970targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 0 _ (by rfl)
  have c9r6971_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] := by
    let c9r6971targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)]]
    let c9r6971choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6971targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3)] c9r6971choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6971targets, c9r6971choice, ?_, checked⟩
    intro S h
    simp only [c9r6971targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 2 _ (by rfl)
  have c9r6972_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] := by
    let c9r6972targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)]]
    let c9r6972choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6972targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,4)] c9r6972choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6972targets, c9r6972choice, ?_, checked⟩
    intro S h
    simp only [c9r6972targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 4 _ (by rfl)
  have c9r6973_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r6973targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r6973choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6973targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r6973choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6973targets, c9r6973choice, ?_, checked⟩
    intro S h
    simp only [c9r6973targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 8 _ (by rfl)
  have c9r6974_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] := by
    let c9r6974targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,2)],[(0,3),(0,4),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(4,2)]]
    let c9r6974choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6974targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2)] c9r6974choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6974targets, c9r6974choice, ?_, checked⟩
    intro S h
    simp only [c9r6974targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 11 _ (by rfl)
  have c9r6975_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] := by
    let c9r6975targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,1),(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(0,4),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,2),(0,3),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)],[(0,3),(0,4),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4),(3,1),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,3)],[(0,3),(0,4),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,2),(3,3)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(3,4)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,0)],[(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3),(4,3)]]
    let c9r6975choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6975targets [(0,2),(0,3),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,3)] c9r6975choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6975targets, c9r6975choice, ?_, checked⟩
    intro S h
    simp only [c9r6975targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,true,true,false] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6968_closed
  · subst row; exact c9r6969_closed
  · subst row; exact c9r6970_closed
  · subst row; exact c9r6971_closed
  · subst row; exact c9r6972_closed
  · subst row; exact c9r6973_closed
  · subst row; exact c9r6974_closed
  · subst row; exact c9r6975_closed
theorem C9R06944_closed (row : List GridPoint) (h : FamilyMember row F9B003L25) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L25, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06944G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06944G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06944G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06944G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06944G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06944G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06944G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06944G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06944G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06944G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06944G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06944G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06944G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06944G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06944G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06944G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06944G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06944G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06944G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06944G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06944G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06944G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06944G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06944G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06944G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06944G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06944G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06944G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06944G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06944G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06944G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06944G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
