import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R05280G0 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5280_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)] := by
    let c9r5280targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,0),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,0),(5,1)],[(0,2),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,0)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)]]
    let c9r5280choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5280targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1)] c9r5280choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5280targets, c9r5280choice, ?_, checked⟩
    intro S h
    simp only [c9r5280targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 24 _ (by rfl)
  have c9r5281_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)] := by
    let c9r5281targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,2)]]
    let c9r5281choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5281targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2)] c9r5281choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5281targets, c9r5281choice, ?_, checked⟩
    intro S h
    simp only [c9r5281targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 27 _ (by rfl)
  have c9r5282_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)] := by
    let c9r5282targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1),(7,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2),(4,2),(5,2),(6,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,1),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,0),(3,1),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,0),(4,1),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(4,2),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,0),(5,1),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(5,2),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,0),(6,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(6,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)]]
    let c9r5282choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 7 ∨ (b.1 = 7 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5282targets [(0,1),(1,0),(1,1),(1,2),(2,1),(3,1),(4,1),(5,1),(6,1)] c9r5282choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5282targets, c9r5282choice, ?_, checked⟩
    intro S h
    simp only [c9r5282targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 30 _ (by rfl)
  have c9r5283_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)] := by
    let c9r5283targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(1,6),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,6)]]
    let c9r5283choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (2,(0,0)) else (3,(0,1)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 6) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 7) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r5283targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6)] c9r5283choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5283targets, c9r5283choice, ?_, checked⟩
    intro S h
    simp only [c9r5283targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 4 _ (by rfl)
  have c9r5284_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)] := by
    let c9r5284targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)]]
    let c9r5284choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5284targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2)] c9r5284choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5284targets, c9r5284choice, ?_, checked⟩
    intro S h
    simp only [c9r5284targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 9 _ (by rfl)
  have c9r5285_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)] := by
    let c9r5285targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)]]
    let c9r5285choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5285targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3)] c9r5285choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5285targets, c9r5285choice, ?_, checked⟩
    intro S h
    simp only [c9r5285targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 12 _ (by rfl)
  have c9r5286_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)] := by
    let c9r5286targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)]]
    let c9r5286choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5286targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4)] c9r5286choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5286targets, c9r5286choice, ?_, checked⟩
    intro S h
    simp only [c9r5286targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 14 _ (by rfl)
  have c9r5287_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)] := by
    let c9r5287targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(2,6),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,5),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(2,5),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(2,6),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5),(4,5)]]
    let c9r5287choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5287targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,5)] c9r5287choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5287targets, c9r5287choice, ?_, checked⟩
    intro S h
    simp only [c9r5287targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 16 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5280_closed
  · subst row; exact c9r5281_closed
  · subst row; exact c9r5282_closed
  · subst row; exact c9r5283_closed
  · subst row; exact c9r5284_closed
  · subst row; exact c9r5285_closed
  · subst row; exact c9r5286_closed
  · subst row; exact c9r5287_closed
theorem C9R05280G1 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5288_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)] := by
    let c9r5288targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)]]
    let c9r5288choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5288targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2)] c9r5288choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5288targets, c9r5288choice, ?_, checked⟩
    intro S h
    simp only [c9r5288targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 21 _ (by rfl)
  have c9r5289_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)] := by
    let c9r5289targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)]]
    let c9r5289choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5289targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3)] c9r5289choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5289targets, c9r5289choice, ?_, checked⟩
    intro S h
    simp only [c9r5289targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 24 _ (by rfl)
  have c9r5290_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)] := by
    let c9r5290targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)]]
    let c9r5290choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5290targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4)] c9r5290choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5290targets, c9r5290choice, ?_, checked⟩
    intro S h
    simp only [c9r5290targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 27 _ (by rfl)
  have c9r5291_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)] := by
    let c9r5291targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)]]
    let c9r5291choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5291targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2)] c9r5291choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5291targets, c9r5291choice, ?_, checked⟩
    intro S h
    simp only [c9r5291targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 30 _ (by rfl)
  have c9r5292_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)] := by
    let c9r5292targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]]
    let c9r5292choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5292targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4)] c9r5292choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5292targets, c9r5292choice, ?_, checked⟩
    intro S h
    simp only [c9r5292targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 1 _ (by rfl)
  have c9r5293_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)] := by
    let c9r5293targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)]]
    let c9r5293choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5293targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3)] c9r5293choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5293targets, c9r5293choice, ?_, checked⟩
    intro S h
    simp only [c9r5293targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 4 _ (by rfl)
  have c9r5294_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)] := by
    let c9r5294targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(4,5)]]
    let c9r5294choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5294targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5)] c9r5294choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5294targets, c9r5294choice, ?_, checked⟩
    intro S h
    simp only [c9r5294targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 7 _ (by rfl)
  have c9r5295_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)] := by
    let c9r5295targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4),(5,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(2,5),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(2,4),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(2,5),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4),(5,4)]]
    let c9r5295choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5295targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,4),(4,4)] c9r5295choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5295targets, c9r5295choice, ?_, checked⟩
    intro S h
    simp only [c9r5295targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 10 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5288_closed
  · subst row; exact c9r5289_closed
  · subst row; exact c9r5290_closed
  · subst row; exact c9r5291_closed
  · subst row; exact c9r5292_closed
  · subst row; exact c9r5293_closed
  · subst row; exact c9r5294_closed
  · subst row; exact c9r5295_closed
theorem C9R05280G2 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5296_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r5296targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,2),(1,1),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r5296choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5296targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r5296choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5296targets, c9r5296choice, ?_, checked⟩
    intro S h
    simp only [c9r5296targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,true,true,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 15 _ (by rfl)
  have c9r5297_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r5297targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(4,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r5297choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5297targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3)] c9r5297choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5297targets, c9r5297choice, ?_, checked⟩
    intro S h
    simp only [c9r5297targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 19 _ (by rfl)
  have c9r5298_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)] := by
    let c9r5298targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,1)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(5,1)]]
    let c9r5298choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5298targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1)] c9r5298choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5298targets, c9r5298choice, ?_, checked⟩
    intro S h
    simp only [c9r5298targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 22 _ (by rfl)
  have c9r5299_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)] := by
    let c9r5299targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)]]
    let c9r5299choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5299targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2)] c9r5299choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5299targets, c9r5299choice, ?_, checked⟩
    intro S h
    simp only [c9r5299targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 24 _ (by rfl)
  have c9r5300_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)] := by
    let c9r5300targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)]]
    let c9r5300choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5300targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)] c9r5300choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5300targets, c9r5300choice, ?_, checked⟩
    intro S h
    simp only [c9r5300targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 28 _ (by rfl)
  have c9r5301_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)] := by
    let c9r5301targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)]]
    let c9r5301choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5301targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2)] c9r5301choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5301targets, c9r5301choice, ?_, checked⟩
    intro S h
    simp only [c9r5301targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 31 _ (by rfl)
  have c9r5302_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)] := by
    let c9r5302targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)]]
    let c9r5302choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5302targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3)] c9r5302choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5302targets, c9r5302choice, ?_, checked⟩
    intro S h
    simp only [c9r5302targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 1 _ (by rfl)
  have c9r5303_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)] := by
    let c9r5303targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,1),(5,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,1)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)]]
    let c9r5303choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5303targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2)] c9r5303choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5303targets, c9r5303choice, ?_, checked⟩
    intro S h
    simp only [c9r5303targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 5 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5296_closed
  · subst row; exact c9r5297_closed
  · subst row; exact c9r5298_closed
  · subst row; exact c9r5299_closed
  · subst row; exact c9r5300_closed
  · subst row; exact c9r5301_closed
  · subst row; exact c9r5302_closed
  · subst row; exact c9r5303_closed
theorem C9R05280G3 (row : List GridPoint) (h : row ∈ [[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r5304_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)] := by
    let c9r5304targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,3)]]
    let c9r5304choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5304targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3)] c9r5304choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5304targets, c9r5304choice, ?_, checked⟩
    intro S h
    simp only [c9r5304targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 8 _ (by rfl)
  have c9r5305_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)] := by
    let c9r5305targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2),(6,2)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,1),(3,2),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,1),(4,2),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,1),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2),(6,2)]]
    let c9r5305choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5305targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(4,2),(5,2)] c9r5305choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5305targets, c9r5305choice, ?_, checked⟩
    intro S h
    simp only [c9r5305targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 11 _ (by rfl)
  have c9r5306_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)] := by
    let c9r5306targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(4,5)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,5),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(3,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(3,6)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,5)]]
    let c9r5306choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5306targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5)] c9r5306choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5306targets, c9r5306choice, ?_, checked⟩
    intro S h
    simp only [c9r5306targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 15 _ (by rfl)
  have c9r5307_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)] := by
    let c9r5307targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)]]
    let c9r5307choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5307targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3)] c9r5307choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5307targets, c9r5307choice, ?_, checked⟩
    intro S h
    simp only [c9r5307targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 18 _ (by rfl)
  have c9r5308_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)] := by
    let c9r5308targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4),(5,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(3,5),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(3,5),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4),(5,4)]]
    let c9r5308choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r5308targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,4)] c9r5308choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5308targets, c9r5308choice, ?_, checked⟩
    intro S h
    simp only [c9r5308targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 20 _ (by rfl)
  have c9r5309_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)] := by
    let c9r5309targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,2),(5,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,1),(4,2),(4,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(5,2)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)]]
    let c9r5309choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5309targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3)] c9r5309choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5309targets, c9r5309choice, ?_, checked⟩
    intro S h
    simp only [c9r5309targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 24 _ (by rfl)
  have c9r5310_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)] := by
    let c9r5310targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(5,4)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(4,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(4,5)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(5,4)]]
    let c9r5310choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r5310targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4)] c9r5310choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5310targets, c9r5310choice, ?_, checked⟩
    intro S h
    simp only [c9r5310targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 27 _ (by rfl)
  have c9r5311_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)] := by
    let c9r5311targets : Array (List GridPoint) := #[[(0,1),(1,1),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3),(6,3)],[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(0,2),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,2),(1,0),(1,1),(1,2),(1,3),(2,3),(2,4),(3,4),(4,4),(5,4)],[(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,0),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(2,4),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(3,4),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,2),(4,3),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(4,4),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,2),(5,3)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3),(5,4)],[(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3),(6,3)]]
    let c9r5311choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < -1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 0) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 3) then (3,(0,1)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 4) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r5311targets [(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,3),(4,3),(5,3)] c9r5311choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r5311targets, c9r5311choice, ?_, checked⟩
    intro S h
    simp only [c9r5311targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,false,false,true,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,false,true,false,false,true,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,true,false,true,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,false,true,false,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,false,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [false,true,true,true,true,true,true,true,false,true,true] 30 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r5304_closed
  · subst row; exact c9r5305_closed
  · subst row; exact c9r5306_closed
  · subst row; exact c9r5307_closed
  · subst row; exact c9r5308_closed
  · subst row; exact c9r5309_closed
  · subst row; exact c9r5310_closed
  · subst row; exact c9r5311_closed
theorem C9R05280_closed (row : List GridPoint) (h : FamilyMember row F9B002L37) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B002L37, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R05280G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05280G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05280G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05280G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05280G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05280G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05280G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05280G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05280G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05280G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05280G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05280G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05280G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05280G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05280G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05280G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05280G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05280G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05280G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05280G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05280G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05280G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05280G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05280G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R05280G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R05280G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R05280G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R05280G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R05280G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R05280G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R05280G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R05280G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
