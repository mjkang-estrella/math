import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R04128G0 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4128_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] := by
    let c9r4128targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)]]
    let c9r4128choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4128targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2)] c9r4128choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4128targets, c9r4128choice, ?_, checked⟩
    intro S h
    simp only [c9r4128targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 25 _ (by rfl)
  have c9r4129_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] := by
    let c9r4129targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)]]
    let c9r4129choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4129targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0)] c9r4129choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4129targets, c9r4129choice, ?_, checked⟩
    intro S h
    simp only [c9r4129targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 27 _ (by rfl)
  have c9r4130_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] := by
    let c9r4130targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)]]
    let c9r4130choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4130targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1)] c9r4130choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4130targets, c9r4130choice, ?_, checked⟩
    intro S h
    simp only [c9r4130targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 29 _ (by rfl)
  have c9r4131_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] := by
    let c9r4131targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,1)]]
    let c9r4131choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4131targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1)] c9r4131choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4131targets, c9r4131choice, ?_, checked⟩
    intro S h
    simp only [c9r4131targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 0 _ (by rfl)
  have c9r4132_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] := by
    let c9r4132targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,0),(4,0),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(4,0),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(4,1),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0),(6,0)]]
    let c9r4132choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4132targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(4,0),(5,0)] c9r4132choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4132targets, c9r4132choice, ?_, checked⟩
    intro S h
    simp only [c9r4132targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 2 _ (by rfl)
  have c9r4133_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] := by
    let c9r4133targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,3)]]
    let c9r4133choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4133targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3)] c9r4133choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4133targets, c9r4133choice, ?_, checked⟩
    intro S h
    simp only [c9r4133targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 6 _ (by rfl)
  have c9r4134_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] := by
    let c9r4134targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)]]
    let c9r4134choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4134targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1)] c9r4134choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4134targets, c9r4134choice, ?_, checked⟩
    intro S h
    simp only [c9r4134targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 9 _ (by rfl)
  have c9r4135_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] := by
    let c9r4135targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2),(5,2)]]
    let c9r4135choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4135targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,2)] c9r4135choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4135targets, c9r4135choice, ?_, checked⟩
    intro S h
    simp only [c9r4135targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4128_closed
  · subst row; exact c9r4129_closed
  · subst row; exact c9r4130_closed
  · subst row; exact c9r4131_closed
  · subst row; exact c9r4132_closed
  · subst row; exact c9r4133_closed
  · subst row; exact c9r4134_closed
  · subst row; exact c9r4135_closed
theorem C9R04128G1 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4136_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] := by
    let c9r4136targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)]]
    let c9r4136choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4136targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1)] c9r4136choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4136targets, c9r4136choice, ?_, checked⟩
    intro S h
    simp only [c9r4136targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 14 _ (by rfl)
  have c9r4137_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] := by
    let c9r4137targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,2)]]
    let c9r4137choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4137targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2)] c9r4137choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4137targets, c9r4137choice, ?_, checked⟩
    intro S h
    simp only [c9r4137targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 17 _ (by rfl)
  have c9r4138_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] := by
    let c9r4138targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,0),(2,1),(3,1),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)]]
    let c9r4138choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4138targets [(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,1)] c9r4138choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4138targets, c9r4138choice, ?_, checked⟩
    intro S h
    simp only [c9r4138targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 20 _ (by rfl)
  have c9r4139_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] := by
    let c9r4139targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)]]
    let c9r4139choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4139targets [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1)] c9r4139choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4139targets, c9r4139choice, ?_, checked⟩
    intro S h
    simp only [c9r4139targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 25 _ (by rfl)
  have c9r4140_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] := by
    let c9r4140targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)]]
    let c9r4140choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4140targets [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2)] c9r4140choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4140targets, c9r4140choice, ?_, checked⟩
    intro S h
    simp only [c9r4140targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 30 _ (by rfl)
  have c9r4141_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] := by
    let c9r4141targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)]]
    let c9r4141choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4141targets [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0)] c9r4141choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4141targets, c9r4141choice, ?_, checked⟩
    intro S h
    simp only [c9r4141targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 0 _ (by rfl)
  have c9r4142_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] := by
    let c9r4142targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]
    let c9r4142choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4142targets [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1)] c9r4142choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4142targets, c9r4142choice, ?_, checked⟩
    intro S h
    simp only [c9r4142targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 2 _ (by rfl)
  have c9r4143_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c9r4143targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c9r4143choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4143targets [(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1)] c9r4143choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4143targets, c9r4143choice, ?_, checked⟩
    intro S h
    simp only [c9r4143targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 6 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4136_closed
  · subst row; exact c9r4137_closed
  · subst row; exact c9r4138_closed
  · subst row; exact c9r4139_closed
  · subst row; exact c9r4140_closed
  · subst row; exact c9r4141_closed
  · subst row; exact c9r4142_closed
  · subst row; exact c9r4143_closed
theorem C9R04128G2 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4144_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r4144targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r4144choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4144targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3)] c9r4144choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4144targets, c9r4144choice, ?_, checked⟩
    intro S h
    simp only [c9r4144targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 14 _ (by rfl)
  have c9r4145_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r4145targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r4145choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4145targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0)] c9r4145choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4145targets, c9r4145choice, ?_, checked⟩
    intro S h
    simp only [c9r4145targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 17 _ (by rfl)
  have c9r4146_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r4146targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r4146choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r4146targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1)] c9r4146choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4146targets, c9r4146choice, ?_, checked⟩
    intro S h
    simp only [c9r4146targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 19 _ (by rfl)
  have c9r4147_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r4147targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r4147choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4147targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,2)] c9r4147choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4147targets, c9r4147choice, ?_, checked⟩
    intro S h
    simp only [c9r4147targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 21 _ (by rfl)
  have c9r4148_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r4148targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r4148choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4148targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1)] c9r4148choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4148targets, c9r4148choice, ?_, checked⟩
    intro S h
    simp only [c9r4148targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 24 _ (by rfl)
  have c9r4149_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r4149targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,0),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r4149choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4149targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(5,0)] c9r4149choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4149targets, c9r4149choice, ?_, checked⟩
    intro S h
    simp only [c9r4149targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 26 _ (by rfl)
  have c9r4150_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r4150targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r4150choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4150targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2)] c9r4150choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4150targets, c9r4150choice, ?_, checked⟩
    intro S h
    simp only [c9r4150targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 29 _ (by rfl)
  have c9r4151_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r4151targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,0),(3,1),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r4151choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4151targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,1)] c9r4151choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4151targets, c9r4151choice, ?_, checked⟩
    intro S h
    simp only [c9r4151targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 0 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4144_closed
  · subst row; exact c9r4145_closed
  · subst row; exact c9r4146_closed
  · subst row; exact c9r4147_closed
  · subst row; exact c9r4148_closed
  · subst row; exact c9r4149_closed
  · subst row; exact c9r4150_closed
  · subst row; exact c9r4151_closed
theorem C9R04128G3 (row : List GridPoint) (h : row ∈ [[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r4152_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r4152targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r4152choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r4152targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1)] c9r4152choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4152targets, c9r4152choice, ?_, checked⟩
    intro S h
    simp only [c9r4152targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 4 _ (by rfl)
  have c9r4153_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r4153targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r4153choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4153targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2)] c9r4153choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4153targets, c9r4153choice, ?_, checked⟩
    intro S h
    simp only [c9r4153targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 9 _ (by rfl)
  have c9r4154_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r4154targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r4154choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4154targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0)] c9r4154choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4154targets, c9r4154choice, ?_, checked⟩
    intro S h
    simp only [c9r4154targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 11 _ (by rfl)
  have c9r4155_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r4155targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r4155choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r4155targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,1)] c9r4155choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4155targets, c9r4155choice, ?_, checked⟩
    intro S h
    simp only [c9r4155targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 13 _ (by rfl)
  have c9r4156_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r4156targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,2),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(0,4),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,0),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r4156choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (2,(1,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (13,(0,0)) else (14,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r4156targets [(0,1),(0,2),(0,3),(1,1),(2,1),(3,1),(4,1),(5,0),(5,1)] c9r4156choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4156targets, c9r4156choice, ?_, checked⟩
    intro S h
    simp only [c9r4156targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 17 _ (by rfl)
  have c9r4157_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] := by
    let c9r4157targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2)],[(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2)]]
    let c9r4157choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4157targets [(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2)] c9r4157choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4157targets, c9r4157choice, ?_, checked⟩
    intro S h
    simp only [c9r4157targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 24 _ (by rfl)
  have c9r4158_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] := by
    let c9r4158targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,3)]]
    let c9r4158choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4158targets [(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)] c9r4158choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4158targets, c9r4158choice, ?_, checked⟩
    intro S h
    simp only [c9r4158targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 31 _ (by rfl)
  have c9r4159_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] := by
    let c9r4159targets : Array (List GridPoint) := #[[(0,1),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)],[(0,1),(0,2),(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,0)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0)],[(0,2),(0,3),(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2)],[(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(4,0)]]
    let c9r4159choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (1,(1,0)) else (2,(1,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r4159targets [(0,1),(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0)] c9r4159choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r4159targets, c9r4159choice, ?_, checked⟩
    intro S h
    simp only [c9r4159targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,false,true,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,false,false,true,true,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,false,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,false,true,true] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r4152_closed
  · subst row; exact c9r4153_closed
  · subst row; exact c9r4154_closed
  · subst row; exact c9r4155_closed
  · subst row; exact c9r4156_closed
  · subst row; exact c9r4157_closed
  · subst row; exact c9r4158_closed
  · subst row; exact c9r4159_closed
theorem C9R04128_closed (row : List GridPoint) (h : FamilyMember row F9B002L1) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L1, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R04128G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04128G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04128G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04128G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04128G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04128G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04128G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04128G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04128G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04128G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04128G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04128G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04128G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04128G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04128G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04128G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04128G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04128G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04128G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04128G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04128G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04128G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04128G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04128G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R04128G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R04128G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R04128G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R04128G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R04128G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R04128G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R04128G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R04128G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
