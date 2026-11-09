import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R06912G0 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6912_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r6912targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r6912choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6912targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r6912choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6912targets, c9r6912choice, ?_, checked⟩
    intro S h
    simp only [c9r6912targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 9 _ (by rfl)
  have c9r6913_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r6913targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r6913choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6913targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r6913choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6913targets, c9r6913choice, ?_, checked⟩
    intro S h
    simp only [c9r6913targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 12 _ (by rfl)
  have c9r6914_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r6914targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r6914choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r6914targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r6914choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6914targets, c9r6914choice, ?_, checked⟩
    intro S h
    simp only [c9r6914targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 14 _ (by rfl)
  have c9r6915_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r6915targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r6915choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6915targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r6915choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6915targets, c9r6915choice, ?_, checked⟩
    intro S h
    simp only [c9r6915targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 16 _ (by rfl)
  have c9r6916_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r6916targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r6916choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6916targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] c9r6916choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6916targets, c9r6916choice, ?_, checked⟩
    intro S h
    simp only [c9r6916targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 19 _ (by rfl)
  have c9r6917_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r6917targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r6917choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6917targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] c9r6917choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6917targets, c9r6917choice, ?_, checked⟩
    intro S h
    simp only [c9r6917targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 21 _ (by rfl)
  have c9r6918_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r6918targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r6918choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6918targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] c9r6918choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6918targets, c9r6918choice, ?_, checked⟩
    intro S h
    simp only [c9r6918targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 24 _ (by rfl)
  have c9r6919_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r6919targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r6919choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6919targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] c9r6919choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6919targets, c9r6919choice, ?_, checked⟩
    intro S h
    simp only [c9r6919targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 27 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6912_closed
  · subst row; exact c9r6913_closed
  · subst row; exact c9r6914_closed
  · subst row; exact c9r6915_closed
  · subst row; exact c9r6916_closed
  · subst row; exact c9r6917_closed
  · subst row; exact c9r6918_closed
  · subst row; exact c9r6919_closed
theorem C9R06912G1 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6920_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r6920targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r6920choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6920targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] c9r6920choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6920targets, c9r6920choice, ?_, checked⟩
    intro S h
    simp only [c9r6920targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 0 _ (by rfl)
  have c9r6921_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] := by
    let c9r6921targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6921choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6921targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)] c9r6921choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6921targets, c9r6921choice, ?_, checked⟩
    intro S h
    simp only [c9r6921targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 5 _ (by rfl)
  have c9r6922_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] := by
    let c9r6922targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(6,0)]]
    let c9r6922choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (11,(0,0)) else (12,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6922targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)] c9r6922choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6922targets, c9r6922choice, ?_, checked⟩
    intro S h
    simp only [c9r6922targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 7 _ (by rfl)
  have c9r6923_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] := by
    let c9r6923targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1),(6,1)]]
    let c9r6923choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6923targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)] c9r6923choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6923targets, c9r6923choice, ?_, checked⟩
    intro S h
    simp only [c9r6923targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 9 _ (by rfl)
  have c9r6924_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r6924targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,1),(5,1),(6,0),(6,1)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r6924choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6924targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)] c9r6924choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6924targets, c9r6924choice, ?_, checked⟩
    intro S h
    simp only [c9r6924targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 13 _ (by rfl)
  have c9r6925_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r6925targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6925choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6925targets [(0,2),(0,3),(1,2),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)] c9r6925choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6925targets, c9r6925choice, ?_, checked⟩
    intro S h
    simp only [c9r6925targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 19 _ (by rfl)
  have c9r6926_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)] := by
    let c9r6926targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)]]
    let c9r6926choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6926targets [(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)] c9r6926choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6926targets, c9r6926choice, ?_, checked⟩
    intro S h
    simp only [c9r6926targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 27 _ (by rfl)
  have c9r6927_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r6927targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r6927choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6927targets [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r6927choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6927targets, c9r6927choice, ?_, checked⟩
    intro S h
    simp only [c9r6927targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6920_closed
  · subst row; exact c9r6921_closed
  · subst row; exact c9r6922_closed
  · subst row; exact c9r6923_closed
  · subst row; exact c9r6924_closed
  · subst row; exact c9r6925_closed
  · subst row; exact c9r6926_closed
  · subst row; exact c9r6927_closed
theorem C9R06912G2 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6928_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r6928targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r6928choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6928targets [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)] c9r6928choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6928targets, c9r6928choice, ?_, checked⟩
    intro S h
    simp only [c9r6928targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 5 _ (by rfl)
  have c9r6929_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r6929targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r6929choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6929targets [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)] c9r6929choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6929targets, c9r6929choice, ?_, checked⟩
    intro S h
    simp only [c9r6929targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 7 _ (by rfl)
  have c9r6930_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r6930targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r6930choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6930targets [(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)] c9r6930choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6930targets, c9r6930choice, ?_, checked⟩
    intro S h
    simp only [c9r6930targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 9 _ (by rfl)
  have c9r6931_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r6931targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r6931choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r6931targets [(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)] c9r6931choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6931targets, c9r6931choice, ?_, checked⟩
    intro S h
    simp only [c9r6931targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 14 _ (by rfl)
  have c9r6932_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r6932targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r6932choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6932targets [(0,2),(0,3),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)] c9r6932choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6932targets, c9r6932choice, ?_, checked⟩
    intro S h
    simp only [c9r6932targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 20 _ (by rfl)
  have c9r6933_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r6933targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,2),(0,3),(1,2),(2,2),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r6933choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6933targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r6933choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6933targets, c9r6933choice, ?_, checked⟩
    intro S h
    simp only [c9r6933targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 30 _ (by rfl)
  have c9r6934_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r6934targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(0,4),(1,3),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r6934choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6934targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r6934choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6934targets, c9r6934choice, ?_, checked⟩
    intro S h
    simp only [c9r6934targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 2 _ (by rfl)
  have c9r6935_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r6935targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r6935choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6935targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r6935choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6935targets, c9r6935choice, ?_, checked⟩
    intro S h
    simp only [c9r6935targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6928_closed
  · subst row; exact c9r6929_closed
  · subst row; exact c9r6930_closed
  · subst row; exact c9r6931_closed
  · subst row; exact c9r6932_closed
  · subst row; exact c9r6933_closed
  · subst row; exact c9r6934_closed
  · subst row; exact c9r6935_closed
theorem C9R06912G3 (row : List GridPoint) (h : row ∈ [[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r6936_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r6936targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r6936choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6936targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r6936choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6936targets, c9r6936choice, ?_, checked⟩
    intro S h
    simp only [c9r6936targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 7 _ (by rfl)
  have c9r6937_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r6937targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r6937choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6937targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r6937choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6937targets, c9r6937choice, ?_, checked⟩
    intro S h
    simp only [c9r6937targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 9 _ (by rfl)
  have c9r6938_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r6938targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r6938choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6938targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)] c9r6938choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6938targets, c9r6938choice, ?_, checked⟩
    intro S h
    simp only [c9r6938targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 12 _ (by rfl)
  have c9r6939_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] := by
    let c9r6939targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)]]
    let c9r6939choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6939targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)] c9r6939choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6939targets, c9r6939choice, ?_, checked⟩
    intro S h
    simp only [c9r6939targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 15 _ (by rfl)
  have c9r6940_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)] := by
    let c9r6940targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)],[(0,3),(0,4),(1,3),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(5,0)],[(0,3),(0,4),(1,3),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0),(6,0)]]
    let c9r6940choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,1)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r6940targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)] c9r6940choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6940targets, c9r6940choice, ?_, checked⟩
    intro S h
    simp only [c9r6940targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 17 _ (by rfl)
  have c9r6941_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r6941targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r6941choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (1,(1,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r6941targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)] c9r6941choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6941targets, c9r6941choice, ?_, checked⟩
    intro S h
    simp only [c9r6941targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 20 _ (by rfl)
  have c9r6942_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r6942targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r6942choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6942targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)] c9r6942choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6942targets, c9r6942choice, ?_, checked⟩
    intro S h
    simp only [c9r6942targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 23 _ (by rfl)
  have c9r6943_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r6943targets : Array (List GridPoint) := #[[(0,2),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,3),(1,2),(1,3),(2,2),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,1),(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(0,4),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,1),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r6943choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 1) then (if b.1 < -1 ∨ (b.1 = -1 ∧ b.2 < 3) then (0,(1,0)) else (1,(1,0))) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r6943targets [(0,2),(0,3),(1,2),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)] c9r6943choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r6943targets, c9r6943choice, ?_, checked⟩
    intro S h
    simp only [c9r6943targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,false,false,true,false,false,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,false,true,true,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,false,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,false,false,false,true] 26 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r6936_closed
  · subst row; exact c9r6937_closed
  · subst row; exact c9r6938_closed
  · subst row; exact c9r6939_closed
  · subst row; exact c9r6940_closed
  · subst row; exact c9r6941_closed
  · subst row; exact c9r6942_closed
  · subst row; exact c9r6943_closed
theorem C9R06912_closed (row : List GridPoint) (h : FamilyMember row F9B003L24) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B003L24, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R06912G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06912G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06912G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06912G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06912G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06912G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06912G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06912G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06912G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06912G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06912G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06912G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06912G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06912G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06912G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06912G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06912G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06912G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06912G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06912G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06912G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06912G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06912G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06912G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R06912G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R06912G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R06912G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R06912G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R06912G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R06912G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R06912G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R06912G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
