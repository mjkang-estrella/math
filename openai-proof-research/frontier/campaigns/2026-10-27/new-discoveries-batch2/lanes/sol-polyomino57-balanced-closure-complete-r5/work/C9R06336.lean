import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06336G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6336_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)] := by
    let c9r6336targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)]]
    let c9r6336choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6336targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)] c9r6336choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6336targets, c9r6336choice, ?_, checked⟩
    intro S h
    simp only [c9r6336targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 7 _ (by rfl)
  have c9r6337_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)] := by
    let c9r6337targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)]]
    let c9r6337choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6337targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)] c9r6337choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6337targets, c9r6337choice, ?_, checked⟩
    intro S h
    simp only [c9r6337targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 9 _ (by rfl)
  have c9r6338_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)] := by
    let c9r6338targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)]]
    let c9r6338choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6338targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)] c9r6338choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6338targets, c9r6338choice, ?_, checked⟩
    intro S h
    simp only [c9r6338targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 11 _ (by rfl)
  have c9r6339_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)] := by
    let c9r6339targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,3),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(5,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,3)]]
    let c9r6339choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6339targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)] c9r6339choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6339targets, c9r6339choice, ?_, checked⟩
    intro S h
    simp only [c9r6339targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 15 _ (by rfl)
  have c9r6340_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)] := by
    let c9r6340targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)]]
    let c9r6340choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6340targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)] c9r6340choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6340targets, c9r6340choice, ?_, checked⟩
    intro S h
    simp only [c9r6340targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 18 _ (by rfl)
  have c9r6341_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)] := by
    let c9r6341targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2),(7,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2),(6,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2),(7,2)]]
    let c9r6341choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6341targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)] c9r6341choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6341targets, c9r6341choice, ?_, checked⟩
    intro S h
    simp only [c9r6341targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 20 _ (by rfl)
  have c9r6342_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)] := by
    let c9r6342targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,1),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)]]
    let c9r6342choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6342targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)] c9r6342choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6342targets, c9r6342choice, ?_, checked⟩
    intro S h
    simp only [c9r6342targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 23 _ (by rfl)
  have c9r6343_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)] := by
    let c9r6343targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1),(7,2)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(7,2)]]
    let c9r6343choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6343targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)] c9r6343choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6343targets, c9r6343choice, ?_, checked⟩
    intro S h
    simp only [c9r6343targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 26 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6336_closed
  · subst row; exact c9r6337_closed
  · subst row; exact c9r6338_closed
  · subst row; exact c9r6339_closed
  · subst row; exact c9r6340_closed
  · subst row; exact c9r6341_closed
  · subst row; exact c9r6342_closed
  · subst row; exact c9r6343_closed
theorem C9R06336G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6344_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)] := by
    let c9r6344targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1),(8,1)],[(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(0,2),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,2),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1),(7,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1),(8,1)]]
    let c9r6344choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 8 ∨ (b.1 = 8 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r6344targets [(0,1),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)] c9r6344choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6344targets, c9r6344choice, ?_, checked⟩
    intro S h
    simp only [c9r6344targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 29 _ (by rfl)
  have c9r6345_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)] := by
    let c9r6345targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,0),(5,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,1)]]
    let c9r6345choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6345targets [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)] c9r6345choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6345targets, c9r6345choice, ?_, checked⟩
    intro S h
    simp only [c9r6345targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 3 _ (by rfl)
  have c9r6346_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r6346targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6346choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6346targets [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r6346choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6346targets, c9r6346choice, ?_, checked⟩
    intro S h
    simp only [c9r6346targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 8 _ (by rfl)
  have c9r6347_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)] := by
    let c9r6347targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(4,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,3)]]
    let c9r6347choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6347targets [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)] c9r6347choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6347targets, c9r6347choice, ?_, checked⟩
    intro S h
    simp only [c9r6347targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 12 _ (by rfl)
  have c9r6348_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)] := by
    let c9r6348targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(6,0)]]
    let c9r6348choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6348targets [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)] c9r6348choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6348targets, c9r6348choice, ?_, checked⟩
    intro S h
    simp only [c9r6348targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 14 _ (by rfl)
  have c9r6349_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)] := by
    let c9r6349targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(6,1)]]
    let c9r6349choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6349targets [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)] c9r6349choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6349targets, c9r6349choice, ?_, checked⟩
    intro S h
    simp only [c9r6349targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 16 _ (by rfl)
  have c9r6350_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)] := by
    let c9r6350targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(3,4),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(3,4),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,1)]]
    let c9r6350choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6350targets [(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)] c9r6350choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6350targets, c9r6350choice, ?_, checked⟩
    intro S h
    simp only [c9r6350targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 21 _ (by rfl)
  have c9r6351_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r6351targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r6351choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6351targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)] c9r6351choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6351targets, c9r6351choice, ?_, checked⟩
    intro S h
    simp only [c9r6351targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 28 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6344_closed
  · subst row; exact c9r6345_closed
  · subst row; exact c9r6346_closed
  · subst row; exact c9r6347_closed
  · subst row; exact c9r6348_closed
  · subst row; exact c9r6349_closed
  · subst row; exact c9r6350_closed
  · subst row; exact c9r6351_closed
theorem C9R06336G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6352_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r6352targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r6352choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6352targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)] c9r6352choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6352targets, c9r6352choice, ?_, checked⟩
    intro S h
    simp only [c9r6352targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 31 _ (by rfl)
  have c9r6353_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r6353targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r6353choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6353targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)] c9r6353choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6353targets, c9r6353choice, ?_, checked⟩
    intro S h
    simp only [c9r6353targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 1 _ (by rfl)
  have c9r6354_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r6354targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r6354choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6354targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)] c9r6354choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6354targets, c9r6354choice, ?_, checked⟩
    intro S h
    simp only [c9r6354targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 3 _ (by rfl)
  have c9r6355_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)] := by
    let c9r6355targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,1)]]
    let c9r6355choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6355targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)] c9r6355choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6355targets, c9r6355choice, ?_, checked⟩
    intro S h
    simp only [c9r6355targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 6 _ (by rfl)
  have c9r6356_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)] := by
    let c9r6356targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0),(7,0)]]
    let c9r6356choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6356targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)] c9r6356choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6356targets, c9r6356choice, ?_, checked⟩
    intro S h
    simp only [c9r6356targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 8 _ (by rfl)
  have c9r6357_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)] := by
    let c9r6357targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,2)]]
    let c9r6357choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6357targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)] c9r6357choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6357targets, c9r6357choice, ?_, checked⟩
    intro S h
    simp only [c9r6357targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 11 _ (by rfl)
  have c9r6358_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)] := by
    let c9r6358targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1),(7,1)]]
    let c9r6358choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6358targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)] c9r6358choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6358targets, c9r6358choice, ?_, checked⟩
    intro S h
    simp only [c9r6358targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 14 _ (by rfl)
  have c9r6359_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r6359targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r6359choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6359targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)] c9r6359choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6359targets, c9r6359choice, ?_, checked⟩
    intro S h
    simp only [c9r6359targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 19 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6352_closed
  · subst row; exact c9r6353_closed
  · subst row; exact c9r6354_closed
  · subst row; exact c9r6355_closed
  · subst row; exact c9r6356_closed
  · subst row; exact c9r6357_closed
  · subst row; exact c9r6358_closed
  · subst row; exact c9r6359_closed
theorem C9R06336G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6360_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)] := by
    let c9r6360targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,2)]]
    let c9r6360choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6360targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)] c9r6360choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6360targets, c9r6360choice, ?_, checked⟩
    intro S h
    simp only [c9r6360targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 24 _ (by rfl)
  have c9r6361_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)] := by
    let c9r6361targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(7,0)]]
    let c9r6361choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6361targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)] c9r6361choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6361targets, c9r6361choice, ?_, checked⟩
    intro S h
    simp only [c9r6361targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 26 _ (by rfl)
  have c9r6362_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)] := by
    let c9r6362targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1),(7,1)]]
    let c9r6362choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6362targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)] c9r6362choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6362targets, c9r6362choice, ?_, checked⟩
    intro S h
    simp only [c9r6362targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 28 _ (by rfl)
  have c9r6363_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)] := by
    let c9r6363targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1),(7,1)]]
    let c9r6363choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6363targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)] c9r6363choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6363targets, c9r6363choice, ?_, checked⟩
    intro S h
    simp only [c9r6363targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 0 _ (by rfl)
  have c9r6364_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r6364targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(1,2),(2,2),(3,2),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r6364choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6364targets [(0,1),(1,1),(2,1),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)] c9r6364choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6364targets, c9r6364choice, ?_, checked⟩
    intro S h
    simp only [c9r6364targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 6 _ (by rfl)
  have c9r6365_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r6365targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(1,2),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,0),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(3,1),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,2),(2,2),(3,2),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r6365choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6365targets [(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)] c9r6365choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6365targets, c9r6365choice, ?_, checked⟩
    intro S h
    simp only [c9r6365targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 14 _ (by rfl)
  have c9r6366_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)] := by
    let c9r6366targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,1),(3,1),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,4)]]
    let c9r6366choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (11,(0,1)) else (12,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r6366targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)] c9r6366choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6366targets, c9r6366choice, ?_, checked⟩
    intro S h
    simp only [c9r6366targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 22 _ (by rfl)
  have c9r6367_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)] := by
    let c9r6367targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3),(6,0)],[(0,0),(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(0,2),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,2),(1,2),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(5,3)],[(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0),(6,0)]]
    let c9r6367choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6367targets [(0,1),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)] c9r6367choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6367targets, c9r6367choice, ?_, checked⟩
    intro S h
    simp only [c9r6367targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,true,true,false,true] 26 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6360_closed
  · subst row; exact c9r6361_closed
  · subst row; exact c9r6362_closed
  · subst row; exact c9r6363_closed
  · subst row; exact c9r6364_closed
  · subst row; exact c9r6365_closed
  · subst row; exact c9r6366_closed
  · subst row; exact c9r6367_closed
theorem C9R06336_closed (row : List GridPoint) (h : FamilyMember row F9B003L6) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L6, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06336G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06336G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06336G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06336G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06336G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06336G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06336G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06336G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06336G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06336G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06336G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06336G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06336G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06336G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06336G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06336G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06336G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06336G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06336G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06336G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06336G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06336G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06336G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06336G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06336G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06336G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06336G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06336G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06336G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06336G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06336G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06336G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
