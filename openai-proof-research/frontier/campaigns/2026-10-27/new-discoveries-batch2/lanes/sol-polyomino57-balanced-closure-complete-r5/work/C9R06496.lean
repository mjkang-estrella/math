import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06496G0 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6496_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] := by
    let c9r6496targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)]]
    let c9r6496choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6496targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1)] c9r6496choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6496targets, c9r6496choice, ?_, checked⟩
    intro S h
    simp only [c9r6496targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 13 _ (by rfl)
  have c9r6497_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] := by
    let c9r6497targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)]]
    let c9r6497choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6497targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3)] c9r6497choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6497targets, c9r6497choice, ?_, checked⟩
    intro S h
    simp only [c9r6497targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 17 _ (by rfl)
  have c9r6498_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)] := by
    let c9r6498targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(4,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)]]
    let c9r6498choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6498targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0)] c9r6498choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6498targets, c9r6498choice, ?_, checked⟩
    intro S h
    simp only [c9r6498targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 20 _ (by rfl)
  have c9r6499_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)] := by
    let c9r6499targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)]]
    let c9r6499choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6499targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2)] c9r6499choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6499targets, c9r6499choice, ?_, checked⟩
    intro S h
    simp only [c9r6499targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 23 _ (by rfl)
  have c9r6500_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)] := by
    let c9r6500targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,1)]]
    let c9r6500choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6500targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1)] c9r6500choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6500targets, c9r6500choice, ?_, checked⟩
    intro S h
    simp only [c9r6500targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 26 _ (by rfl)
  have c9r6501_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)] := by
    let c9r6501targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(3,0),(4,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,0),(4,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(3,1),(4,0)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0),(5,0)]]
    let c9r6501choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6501targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(3,0),(4,0)] c9r6501choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6501targets, c9r6501choice, ?_, checked⟩
    intro S h
    simp only [c9r6501targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 28 _ (by rfl)
  have c9r6502_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)] := by
    let c9r6502targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)]]
    let c9r6502choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6502targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3)] c9r6502choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6502targets, c9r6502choice, ?_, checked⟩
    intro S h
    simp only [c9r6502targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 0 _ (by rfl)
  have c9r6503_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)] := by
    let c9r6503targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)]]
    let c9r6503choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6503targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1)] c9r6503choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6503targets, c9r6503choice, ?_, checked⟩
    intro S h
    simp only [c9r6503targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 3 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6496_closed
  · subst row; exact c9r6497_closed
  · subst row; exact c9r6498_closed
  · subst row; exact c9r6499_closed
  · subst row; exact c9r6500_closed
  · subst row; exact c9r6501_closed
  · subst row; exact c9r6502_closed
  · subst row; exact c9r6503_closed
theorem C9R06496G1 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6504_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)] := by
    let c9r6504targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)]]
    let c9r6504choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6504targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2)] c9r6504choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6504targets, c9r6504choice, ?_, checked⟩
    intro S h
    simp only [c9r6504targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 5 _ (by rfl)
  have c9r6505_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)] := by
    let c9r6505targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)]]
    let c9r6505choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6505targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1)] c9r6505choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6505targets, c9r6505choice, ?_, checked⟩
    intro S h
    simp only [c9r6505targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 8 _ (by rfl)
  have c9r6506_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)] := by
    let c9r6506targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,2)]]
    let c9r6506choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6506targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2)] c9r6506choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6506targets, c9r6506choice, ?_, checked⟩
    intro S h
    simp only [c9r6506targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 11 _ (by rfl)
  have c9r6507_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)] := by
    let c9r6507targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1)]]
    let c9r6507choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6507targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1)] c9r6507choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6507targets, c9r6507choice, ?_, checked⟩
    intro S h
    simp only [c9r6507targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 14 _ (by rfl)
  have c9r6508_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)] := by
    let c9r6508targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4)]]
    let c9r6508choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6508targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4)] c9r6508choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6508targets, c9r6508choice, ?_, checked⟩
    intro S h
    simp only [c9r6508targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 18 _ (by rfl)
  have c9r6509_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)] := by
    let c9r6509targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)]]
    let c9r6509choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6509targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2)] c9r6509choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6509targets, c9r6509choice, ?_, checked⟩
    intro S h
    simp only [c9r6509targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 21 _ (by rfl)
  have c9r6510_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)] := by
    let c9r6510targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3)]]
    let c9r6510choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6510targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3)] c9r6510choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6510targets, c9r6510choice, ?_, checked⟩
    intro S h
    simp only [c9r6510targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 23 _ (by rfl)
  have c9r6511_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)] := by
    let c9r6511targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)]]
    let c9r6511choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6511targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2)] c9r6511choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6511targets, c9r6511choice, ?_, checked⟩
    intro S h
    simp only [c9r6511targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6504_closed
  · subst row; exact c9r6505_closed
  · subst row; exact c9r6506_closed
  · subst row; exact c9r6507_closed
  · subst row; exact c9r6508_closed
  · subst row; exact c9r6509_closed
  · subst row; exact c9r6510_closed
  · subst row; exact c9r6511_closed
theorem C9R06496G2 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6512_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)] := by
    let c9r6512targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(3,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(3,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,3)]]
    let c9r6512choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6512targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3)] c9r6512choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6512targets, c9r6512choice, ?_, checked⟩
    intro S h
    simp only [c9r6512targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 30 _ (by rfl)
  have c9r6513_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)] := by
    let c9r6513targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(2,3),(3,3),(4,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,2),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,2),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,1),(2,2),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(3,3),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(4,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2),(5,2)]]
    let c9r6513choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6513targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,2),(3,2),(4,2)] c9r6513choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6513targets, c9r6513choice, ?_, checked⟩
    intro S h
    simp only [c9r6513targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 1 _ (by rfl)
  have c9r6514_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] := by
    let c9r6514targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)]]
    let c9r6514choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6514targets [(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3)] c9r6514choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6514targets, c9r6514choice, ?_, checked⟩
    intro S h
    simp only [c9r6514targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 7 _ (by rfl)
  have c9r6515_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c9r6515targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,4),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c9r6515choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6515targets [(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2)] c9r6515choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6515targets, c9r6515choice, ?_, checked⟩
    intro S h
    simp only [c9r6515targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 13 _ (by rfl)
  have c9r6516_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2)] := by
    let c9r6516targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,2),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(1,5),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,1),(1,3),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c9r6516choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6516targets [(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2)] c9r6516choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6516targets, c9r6516choice, ?_, checked⟩
    intro S h
    simp only [c9r6516targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 19 _ (by rfl)
  have c9r6517_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r6517targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r6517choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6517targets [(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3)] c9r6517choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6517targets, c9r6517choice, ?_, checked⟩
    intro S h
    simp only [c9r6517targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 24 _ (by rfl)
  have c9r6518_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r6518targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r6518choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6518targets [(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0)] c9r6518choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6518targets, c9r6518choice, ?_, checked⟩
    intro S h
    simp only [c9r6518targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 27 _ (by rfl)
  have c9r6519_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)] := by
    let c9r6519targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1)]]
    let c9r6519choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6519targets [(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1)] c9r6519choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6519targets, c9r6519choice, ?_, checked⟩
    intro S h
    simp only [c9r6519targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 29 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6512_closed
  · subst row; exact c9r6513_closed
  · subst row; exact c9r6514_closed
  · subst row; exact c9r6515_closed
  · subst row; exact c9r6516_closed
  · subst row; exact c9r6517_closed
  · subst row; exact c9r6518_closed
  · subst row; exact c9r6519_closed
theorem C9R06496G3 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6520_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)] := by
    let c9r6520targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,3),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,3),(0,4),(0,5),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2)]]
    let c9r6520choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6520targets [(0,2),(0,3),(0,4),(1,0),(1,2),(2,0),(2,1),(2,2),(3,2)] c9r6520choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6520targets, c9r6520choice, ?_, checked⟩
    intro S h
    simp only [c9r6520targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 31 _ (by rfl)
  have c9r6521_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r6521targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,0),(1,1),(1,4),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,3),(0,4),(0,5),(1,1),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r6521choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6521targets [(0,2),(0,3),(0,4),(1,0),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r6521choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6521targets, c9r6521choice, ?_, checked⟩
    intro S h
    simp only [c9r6521targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 6 _ (by rfl)
  have c9r6522_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] := by
    let c9r6522targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,4)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)]]
    let c9r6522choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6522targets [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1)] c9r6522choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6522targets, c9r6522choice, ?_, checked⟩
    intro S h
    simp only [c9r6522targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 13 _ (by rfl)
  have c9r6523_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] := by
    let c9r6523targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2)]]
    let c9r6523choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r6523targets [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2)] c9r6523choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6523targets, c9r6523choice, ?_, checked⟩
    intro S h
    simp only [c9r6523targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 18 _ (by rfl)
  have c9r6524_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] := by
    let c9r6524targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,3)]]
    let c9r6524choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6524targets [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3)] c9r6524choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6524targets, c9r6524choice, ?_, checked⟩
    intro S h
    simp only [c9r6524targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 22 _ (by rfl)
  have c9r6525_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] := by
    let c9r6525targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(4,0)]]
    let c9r6525choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6525targets [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0)] c9r6525choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6525targets, c9r6525choice, ?_, checked⟩
    intro S h
    simp only [c9r6525targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 24 _ (by rfl)
  have c9r6526_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] := by
    let c9r6526targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1),(4,1)]]
    let c9r6526choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6526targets [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,1)] c9r6526choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6526targets, c9r6526choice, ?_, checked⟩
    intro S h
    simp only [c9r6526targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 26 _ (by rfl)
  have c9r6527_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] := by
    let c9r6527targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,4),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1)],[(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1)]]
    let c9r6527choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 4) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 5) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6527targets [(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1)] c9r6527choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6527targets, c9r6527choice, ?_, checked⟩
    intro S h
    simp only [c9r6527targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,false,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,true,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,false,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,false,false,false] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6520_closed
  · subst row; exact c9r6521_closed
  · subst row; exact c9r6522_closed
  · subst row; exact c9r6523_closed
  · subst row; exact c9r6524_closed
  · subst row; exact c9r6525_closed
  · subst row; exact c9r6526_closed
  · subst row; exact c9r6527_closed
theorem C9R06496_closed (row : List GridPoint) (h : FamilyMember row F9B003L11) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L11, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06496G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06496G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06496G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06496G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06496G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06496G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06496G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06496G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06496G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06496G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06496G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06496G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06496G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06496G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06496G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06496G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06496G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06496G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06496G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06496G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06496G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06496G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06496G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06496G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06496G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06496G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06496G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06496G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06496G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06496G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06496G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06496G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
