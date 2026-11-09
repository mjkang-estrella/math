import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R03648G0 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3648_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r3648targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r3648choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3648targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)] c9r3648choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3648targets, c9r3648choice, ?_, checked⟩
    intro S h
    simp only [c9r3648targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 12 _ (by rfl)
  have c9r3649_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r3649targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r3649choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3649targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)] c9r3649choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3649targets, c9r3649choice, ?_, checked⟩
    intro S h
    simp only [c9r3649targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 15 _ (by rfl)
  have c9r3650_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r3650targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r3650choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r3650targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)] c9r3650choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3650targets, c9r3650choice, ?_, checked⟩
    intro S h
    simp only [c9r3650targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
  have c9r3651_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r3651targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r3651choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3651targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)] c9r3651choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3651targets, c9r3651choice, ?_, checked⟩
    intro S h
    simp only [c9r3651targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 19 _ (by rfl)
  have c9r3652_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)] := by
    let c9r3652targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)]]
    let c9r3652choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3652targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)] c9r3652choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3652targets, c9r3652choice, ?_, checked⟩
    intro S h
    simp only [c9r3652targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 22 _ (by rfl)
  have c9r3653_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)] := by
    let c9r3653targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0),(7,0)]]
    let c9r3653choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3653targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)] c9r3653choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3653targets, c9r3653choice, ?_, checked⟩
    intro S h
    simp only [c9r3653targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 24 _ (by rfl)
  have c9r3654_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)] := by
    let c9r3654targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)]]
    let c9r3654choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3654targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)] c9r3654choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3654targets, c9r3654choice, ?_, checked⟩
    intro S h
    simp only [c9r3654targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 27 _ (by rfl)
  have c9r3655_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)] := by
    let c9r3655targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)]]
    let c9r3655choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3655targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)] c9r3655choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3655targets, c9r3655choice, ?_, checked⟩
    intro S h
    simp only [c9r3655targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 30 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3648_closed
  · subst row; exact c9r3649_closed
  · subst row; exact c9r3650_closed
  · subst row; exact c9r3651_closed
  · subst row; exact c9r3652_closed
  · subst row; exact c9r3653_closed
  · subst row; exact c9r3654_closed
  · subst row; exact c9r3655_closed
theorem C9R03648G1 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3656_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)] := by
    let c9r3656targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,4),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,4)]]
    let c9r3656choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3656targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4)] c9r3656choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3656targets, c9r3656choice, ?_, checked⟩
    intro S h
    simp only [c9r3656targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 3 _ (by rfl)
  have c9r3657_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)] := by
    let c9r3657targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(6,1)]]
    let c9r3657choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3657targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1)] c9r3657choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3657targets, c9r3657choice, ?_, checked⟩
    intro S h
    simp only [c9r3657targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 7 _ (by rfl)
  have c9r3658_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)] := by
    let c9r3658targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(6,2)]]
    let c9r3658choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3658targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2)] c9r3658choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3658targets, c9r3658choice, ?_, checked⟩
    intro S h
    simp only [c9r3658targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 9 _ (by rfl)
  have c9r3659_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)] := by
    let c9r3659targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3),(6,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4),(5,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,3),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3),(6,3)]]
    let c9r3659choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3659targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,3)] c9r3659choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3659targets, c9r3659choice, ?_, checked⟩
    intro S h
    simp only [c9r3659targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 11 _ (by rfl)
  have c9r3660_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r3660targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r3660choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3660targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)] c9r3660choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3660targets, c9r3660choice, ?_, checked⟩
    intro S h
    simp only [c9r3660targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 14 _ (by rfl)
  have c9r3661_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)] := by
    let c9r3661targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)]]
    let c9r3661choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3661targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)] c9r3661choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3661targets, c9r3661choice, ?_, checked⟩
    intro S h
    simp only [c9r3661targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 17 _ (by rfl)
  have c9r3662_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)] := by
    let c9r3662targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(7,1)]]
    let c9r3662choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3662targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)] c9r3662choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3662targets, c9r3662choice, ?_, checked⟩
    intro S h
    simp only [c9r3662targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 20 _ (by rfl)
  have c9r3663_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)] := by
    let c9r3663targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,3)]]
    let c9r3663choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,1)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3663targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3)] c9r3663choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3663targets, c9r3663choice, ?_, checked⟩
    intro S h
    simp only [c9r3663targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 23 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3656_closed
  · subst row; exact c9r3657_closed
  · subst row; exact c9r3658_closed
  · subst row; exact c9r3659_closed
  · subst row; exact c9r3660_closed
  · subst row; exact c9r3661_closed
  · subst row; exact c9r3662_closed
  · subst row; exact c9r3663_closed
theorem C9R03648G2 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3664_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)] := by
    let c9r3664targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2),(7,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3),(6,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2),(6,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2),(7,2)]]
    let c9r3664choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3664targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2),(6,2)] c9r3664choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3664targets, c9r3664choice, ?_, checked⟩
    intro S h
    simp only [c9r3664targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 26 _ (by rfl)
  have c9r3665_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)] := by
    let c9r3665targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(5,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)]]
    let c9r3665choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3665targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)] c9r3665choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3665targets, c9r3665choice, ?_, checked⟩
    intro S h
    simp only [c9r3665targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 31 _ (by rfl)
  have c9r3666_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)] := by
    let c9r3666targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,0)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(7,0)]]
    let c9r3666choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3666targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)] c9r3666choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3666targets, c9r3666choice, ?_, checked⟩
    intro S h
    simp only [c9r3666targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 1 _ (by rfl)
  have c9r3667_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)] := by
    let c9r3667targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)]]
    let c9r3667choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3667targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)] c9r3667choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3667targets, c9r3667choice, ?_, checked⟩
    intro S h
    simp only [c9r3667targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 3 _ (by rfl)
  have c9r3668_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)] := by
    let c9r3668targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,3),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(5,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(5,4)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,3)]]
    let c9r3668choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3668targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)] c9r3668choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3668targets, c9r3668choice, ?_, checked⟩
    intro S h
    simp only [c9r3668targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 7 _ (by rfl)
  have c9r3669_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)] := by
    let c9r3669targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)]]
    let c9r3669choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3669targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)] c9r3669choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3669targets, c9r3669choice, ?_, checked⟩
    intro S h
    simp only [c9r3669targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 10 _ (by rfl)
  have c9r3670_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)] := by
    let c9r3670targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2),(7,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3),(6,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2),(6,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2),(7,2)]]
    let c9r3670choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3670targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)] c9r3670choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3670targets, c9r3670choice, ?_, checked⟩
    intro S h
    simp only [c9r3670targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 12 _ (by rfl)
  have c9r3671_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)] := by
    let c9r3671targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0),(6,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,0),(6,1)],[(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,0)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)]]
    let c9r3671choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < -1) then (12,(0,0)) else (13,(0,1))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3671targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)] c9r3671choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3671targets, c9r3671choice, ?_, checked⟩
    intro S h
    simp only [c9r3671targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3664_closed
  · subst row; exact c9r3665_closed
  · subst row; exact c9r3666_closed
  · subst row; exact c9r3667_closed
  · subst row; exact c9r3668_closed
  · subst row; exact c9r3669_closed
  · subst row; exact c9r3670_closed
  · subst row; exact c9r3671_closed
theorem C9R03648G3 (row : List GridPoint) (h : row ∈ [[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r3672_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)] := by
    let c9r3672targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1),(7,2)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2),(6,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(6,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(6,3)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,2)]]
    let c9r3672choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3672targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)] c9r3672choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3672targets, c9r3672choice, ?_, checked⟩
    intro S h
    simp only [c9r3672targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 18 _ (by rfl)
  have c9r3673_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)] := by
    let c9r3673targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1),(8,1)],[(0,0),(0,1),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(0,1),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,0),(1,1),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2),(7,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,0),(7,1)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1),(7,2)],[(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1),(8,1)]]
    let c9r3673choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (4,(0,0)) else (5,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 0) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 2) then (15,(0,0)) else (if b.1 < 8 ∨ (b.1 = 8 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r3673targets [(0,0),(1,0),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)] c9r3673choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3673targets, c9r3673choice, ?_, checked⟩
    intro S h
    simp only [c9r3673targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 21 _ (by rfl)
  have c9r3674_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)] := by
    let c9r3674targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(1,4),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,1),(1,1),(2,1),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)]]
    let c9r3674choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3674targets [(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)] c9r3674choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3674targets, c9r3674choice, ?_, checked⟩
    intro S h
    simp only [c9r3674targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
  have c9r3675_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r3675targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r3675choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3675targets [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r3675choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3675targets, c9r3675choice, ?_, checked⟩
    intro S h
    simp only [c9r3675targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 0 _ (by rfl)
  have c9r3676_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r3676targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r3676choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3676targets [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)] c9r3676choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3676targets, c9r3676choice, ?_, checked⟩
    intro S h
    simp only [c9r3676targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 3 _ (by rfl)
  have c9r3677_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r3677targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,2)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r3677choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(0,1)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,1)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r3677targets [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)] c9r3677choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3677targets, c9r3677choice, ?_, checked⟩
    intro S h
    simp only [c9r3677targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 5 _ (by rfl)
  have c9r3678_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r3678targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,3)],[(0,0),(0,1),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(1,1),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,1),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r3678choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (6,(0,0)) else (7,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r3678targets [(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)] c9r3678choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3678targets, c9r3678choice, ?_, checked⟩
    intro S h
    simp only [c9r3678targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 7 _ (by rfl)
  have c9r3679_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r3679targets : Array (List GridPoint) := #[[(0,0),(1,0),(2,0),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(0,1),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(1,1),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,0),(1,0),(2,0),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r3679choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < -1) then (0,(1,0)) else (1,(0,1))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r3679targets [(0,0),(1,0),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r3679choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r3679targets, c9r3679choice, ?_, checked⟩
    intro S h
    simp only [c9r3679targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,true,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,false,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,false,true,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,false,false,false,true,true,false] 15 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r3672_closed
  · subst row; exact c9r3673_closed
  · subst row; exact c9r3674_closed
  · subst row; exact c9r3675_closed
  · subst row; exact c9r3676_closed
  · subst row; exact c9r3677_closed
  · subst row; exact c9r3678_closed
  · subst row; exact c9r3679_closed
theorem C9R03648_closed (row : List GridPoint) (h : FamilyMember row F9B001L50) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B001L50, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R03648G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03648G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03648G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03648G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03648G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03648G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03648G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03648G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03648G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03648G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03648G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03648G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03648G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03648G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03648G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03648G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03648G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03648G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03648G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03648G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03648G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03648G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03648G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03648G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R03648G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R03648G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R03648G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R03648G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R03648G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R03648G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R03648G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R03648G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
