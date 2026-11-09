import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R09280G0 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9280_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)] := by
    let c9r9280targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)]]
    let c9r9280choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9280targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)] c9r9280choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9280targets, c9r9280choice, ?_, checked⟩
    intro S h
    simp only [c9r9280targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 5 _ (by rfl)
  have c9r9281_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)] := by
    let c9r9281targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1),(6,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)]]
    let c9r9281choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9281targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)] c9r9281choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9281targets, c9r9281choice, ?_, checked⟩
    intro S h
    simp only [c9r9281targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 8 _ (by rfl)
  have c9r9282_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)] := by
    let c9r9282targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)]]
    let c9r9282choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (7,(0,0)) else (8,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9282targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)] c9r9282choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9282targets, c9r9282choice, ?_, checked⟩
    intro S h
    simp only [c9r9282targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 11 _ (by rfl)
  have c9r9283_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)] := by
    let c9r9283targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2),(6,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)]]
    let c9r9283choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9283targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)] c9r9283choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9283targets, c9r9283choice, ?_, checked⟩
    intro S h
    simp only [c9r9283targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 14 _ (by rfl)
  have c9r9284_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r9284targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,0),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,2),(4,0),(4,1),(4,2)],[(0,4),(1,4),(2,3),(2,4),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,4),(1,4),(2,3),(2,4),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r9284choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,1)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9284targets [(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2)] c9r9284choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9284targets, c9r9284choice, ?_, checked⟩
    intro S h
    simp only [c9r9284targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 20 _ (by rfl)
  have c9r9285_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r9285targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,4),(1,4),(2,3),(2,4),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r9285choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9285targets [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r9285choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9285targets, c9r9285choice, ?_, checked⟩
    intro S h
    simp only [c9r9285targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 26 _ (by rfl)
  have c9r9286_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)] := by
    let c9r9286targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,4),(1,4),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)]]
    let c9r9286choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9286targets [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)] c9r9286choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9286targets, c9r9286choice, ?_, checked⟩
    intro S h
    simp only [c9r9286targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 31 _ (by rfl)
  have c9r9287_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)] := by
    let c9r9287targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,4),(1,4),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,4),(1,4),(2,3),(2,4),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)]]
    let c9r9287choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9287targets [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0)] c9r9287choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9287targets, c9r9287choice, ?_, checked⟩
    intro S h
    simp only [c9r9287targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 1 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9280_closed
  · subst row; exact c9r9281_closed
  · subst row; exact c9r9282_closed
  · subst row; exact c9r9283_closed
  · subst row; exact c9r9284_closed
  · subst row; exact c9r9285_closed
  · subst row; exact c9r9286_closed
  · subst row; exact c9r9287_closed
theorem C9R09280G1 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9288_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)] := by
    let c9r9288targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1),(6,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,4),(1,4),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)]]
    let c9r9288choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9288targets [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)] c9r9288choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9288targets, c9r9288choice, ?_, checked⟩
    intro S h
    simp only [c9r9288targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 3 _ (by rfl)
  have c9r9289_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)] := by
    let c9r9289targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,1),(4,2),(5,1),(6,0),(6,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,4),(1,4),(2,3),(2,4),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(6,0)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1),(6,1)]]
    let c9r9289choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9289targets [(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)] c9r9289choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9289targets, c9r9289choice, ?_, checked⟩
    intro S h
    simp only [c9r9289targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 7 _ (by rfl)
  have c9r9290_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r9290targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,4),(1,4),(2,3),(2,4),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r9290choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9290targets [(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r9290choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9290targets, c9r9290choice, ?_, checked⟩
    intro S h
    simp only [c9r9290targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 15 _ (by rfl)
  have c9r9291_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r9291targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,4),(1,4),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r9291choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9291targets [(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3)] c9r9291choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9291targets, c9r9291choice, ?_, checked⟩
    intro S h
    simp only [c9r9291targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 22 _ (by rfl)
  have c9r9292_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)] := by
    let c9r9292targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,4),(1,4),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,4),(1,4),(2,3),(2,4),(3,3),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(6,0)]]
    let c9r9292choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9292targets [(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0)] c9r9292choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9292targets, c9r9292choice, ?_, checked⟩
    intro S h
    simp only [c9r9292targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 25 _ (by rfl)
  have c9r9293_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)] := by
    let c9r9293targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,4),(1,4),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1),(6,1)]]
    let c9r9293choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9293targets [(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1)] c9r9293choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9293targets, c9r9293choice, ?_, checked⟩
    intro S h
    simp only [c9r9293targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 27 _ (by rfl)
  have c9r9294_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)] := by
    let c9r9294targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2),(6,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)],[(0,4),(1,4),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2),(5,3)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2),(6,2)]]
    let c9r9294choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9294targets [(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,2)] c9r9294choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9294targets, c9r9294choice, ?_, checked⟩
    intro S h
    simp only [c9r9294targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 29 _ (by rfl)
  have c9r9295_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)] := by
    let c9r9295targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,1),(5,2),(6,0),(6,1)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2),(5,0),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,4),(1,4),(2,3),(2,4),(3,3),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(6,0)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(6,1)]]
    let c9r9295choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9295targets [(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1)] c9r9295choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9295targets, c9r9295choice, ?_, checked⟩
    intro S h
    simp only [c9r9295targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 2 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9288_closed
  · subst row; exact c9r9289_closed
  · subst row; exact c9r9290_closed
  · subst row; exact c9r9291_closed
  · subst row; exact c9r9292_closed
  · subst row; exact c9r9293_closed
  · subst row; exact c9r9294_closed
  · subst row; exact c9r9295_closed
theorem C9R09280G2 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9296_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)] := by
    let c9r9296targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,2),(5,2),(6,0),(6,1),(6,2)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,0),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,1),(4,2),(5,0),(5,1),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,4),(1,4),(2,3),(2,4),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(5,3)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,0)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,1)],[(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2),(6,2)]]
    let c9r9296choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,1)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (14,(0,0)) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9296targets [(0,3),(1,3),(2,2),(2,3),(3,2),(4,2),(5,0),(5,1),(5,2)] c9r9296choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9296targets, c9r9296choice, ?_, checked⟩
    intro S h
    simp only [c9r9296targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 8 _ (by rfl)
  have c9r9297_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r9297targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,2),(3,3),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(0,4),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(1,4),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,1),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,4),(1,4),(2,3),(2,4),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r9297choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9297targets [(0,3),(1,3),(2,2),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3)] c9r9297choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9297targets, c9r9297choice, ?_, checked⟩
    intro S h
    simp only [c9r9297targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 16 _ (by rfl)
  have c9r9298_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r9298targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(3,4),(3,5),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,4),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(1,5),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,0),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,1),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,3),(2,3),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,4),(2,4),(2,5),(2,6),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,5)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9298choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 5) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 6) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9298targets [(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3)] c9r9298choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9298targets, c9r9298choice, ?_, checked⟩
    intro S h
    simp only [c9r9298targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 26 _ (by rfl)
  have c9r9299_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)] := by
    let c9r9299targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,4),(1,4),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)]]
    let c9r9299choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9299targets [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)] c9r9299choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9299targets, c9r9299choice, ?_, checked⟩
    intro S h
    simp only [c9r9299targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 3 _ (by rfl)
  have c9r9300_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)] := by
    let c9r9300targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,4),(1,4),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,4),(1,4),(2,4),(2,5),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0),(5,0)]]
    let c9r9300choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9300targets [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0)] c9r9300choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9300targets, c9r9300choice, ?_, checked⟩
    intro S h
    simp only [c9r9300targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 7 _ (by rfl)
  have c9r9301_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)] := by
    let c9r9301targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,4),(1,4),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(5,1)]]
    let c9r9301choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9301targets [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1)] c9r9301choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9301targets, c9r9301choice, ?_, checked⟩
    intro S h
    simp only [c9r9301targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 10 _ (by rfl)
  have c9r9302_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)] := by
    let c9r9302targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,4),(1,4),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2),(5,2)]]
    let c9r9302choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9302targets [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2)] c9r9302choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9302targets, c9r9302choice, ?_, checked⟩
    intro S h
    simp only [c9r9302targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 12 _ (by rfl)
  have c9r9303_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)] := by
    let c9r9303targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3),(5,3)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(1,4),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,4),(1,4),(2,4),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(4,4)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,1),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3),(4,4)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3),(5,3)]]
    let c9r9303choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9303targets [(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,3)] c9r9303choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9303targets, c9r9303choice, ?_, checked⟩
    intro S h
    simp only [c9r9303targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9296_closed
  · subst row; exact c9r9297_closed
  · subst row; exact c9r9298_closed
  · subst row; exact c9r9299_closed
  · subst row; exact c9r9300_closed
  · subst row; exact c9r9301_closed
  · subst row; exact c9r9302_closed
  · subst row; exact c9r9303_closed
theorem C9R09280G3 (row : List GridPoint) (h : row ∈ [[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9304_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)] := by
    let c9r9304targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(3,4),(4,1),(4,2),(4,3),(5,0),(5,1)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(1,4),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,4),(1,4),(2,4),(2,5),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)]]
    let c9r9304choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9304targets [(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1)] c9r9304choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9304targets, c9r9304choice, ?_, checked⟩
    intro S h
    simp only [c9r9304targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 22 _ (by rfl)
  have c9r9305_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)] := by
    let c9r9305targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(3,4),(4,2),(4,3),(5,0),(5,1),(5,2)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(1,4),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(3,4),(4,0),(4,1),(4,2)],[(0,4),(1,4),(2,4),(2,5),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(5,1)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(5,2)]]
    let c9r9305choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9305targets [(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2)] c9r9305choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9305targets, c9r9305choice, ?_, checked⟩
    intro S h
    simp only [c9r9305targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 29 _ (by rfl)
  have c9r9306_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)] := by
    let c9r9306targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(3,4),(4,3),(5,0),(5,1),(5,2),(5,3)],[(0,2),(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(0,4),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(1,4),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,2),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(2,5),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,1),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,2),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,3),(3,4),(4,0),(4,1),(4,2),(4,3)],[(0,4),(1,4),(2,4),(2,5),(3,4),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,0)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,1)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,2)],[(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3),(5,3)]]
    let c9r9306choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9306targets [(0,3),(1,3),(2,3),(2,4),(3,3),(4,0),(4,1),(4,2),(4,3)] c9r9306choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9306targets, c9r9306choice, ?_, checked⟩
    intro S h
    simp only [c9r9306targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 5 _ (by rfl)
  have c9r9307_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] := by
    let c9r9307targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,3),(2,3),(2,5),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)],[(0,4),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,5)]]
    let c9r9307choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0)))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 6) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (15,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 5) then (16,(0,0)) else (17,(0,0)))))))
    have checked : successorFastRowCheck c9r9307targets [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] c9r9307choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9307targets, c9r9307choice, ?_, checked⟩
    intro S h
    simp only [c9r9307targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 17 _ (by rfl)
  have c9r9308_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)] := by
    let c9r9308targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(5,0)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)],[(0,4),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0)],[(0,4),(1,4),(2,4),(3,1),(3,2),(3,3),(3,4),(3,5),(4,0),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(5,0)]]
    let c9r9308choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (14,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (15,(0,0)) else (16,(0,0)))))))
    have checked : successorFastRowCheck c9r9308targets [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0)] c9r9308choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9308targets, c9r9308choice, ?_, checked⟩
    intro S h
    simp only [c9r9308targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 22 _ (by rfl)
  have c9r9309_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)] := by
    let c9r9309targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(5,1)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)],[(0,4),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(5,1)]]
    let c9r9309choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9309targets [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1)] c9r9309choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9309targets, c9r9309choice, ?_, checked⟩
    intro S h
    simp only [c9r9309targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 26 _ (by rfl)
  have c9r9310_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)] := by
    let c9r9310targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(5,2)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)],[(0,4),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,2)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(5,2)]]
    let c9r9310choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9310targets [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2)] c9r9310choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9310targets, c9r9310choice, ?_, checked⟩
    intro S h
    simp only [c9r9310targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 29 _ (by rfl)
  have c9r9311_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)] := by
    let c9r9311targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,3),(3,3),(4,0),(4,1),(4,2),(4,3),(4,4),(5,3)],[(0,2),(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(0,4),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,2),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(1,4),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,3),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)],[(0,4),(1,4),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,0),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,2),(4,3)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(4,4)],[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3),(5,3)]]
    let c9r9311choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 2) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (6,(0,0)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9311targets [(0,3),(1,3),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4),(4,3)] c9r9311choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9311targets, c9r9311choice, ?_, checked⟩
    intro S h
    simp only [c9r9311targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,true,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,true,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,true,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,false,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,true,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,true,true,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,true,true] 31 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9304_closed
  · subst row; exact c9r9305_closed
  · subst row; exact c9r9306_closed
  · subst row; exact c9r9307_closed
  · subst row; exact c9r9308_closed
  · subst row; exact c9r9309_closed
  · subst row; exact c9r9310_closed
  · subst row; exact c9r9311_closed
theorem C9R09280_closed (row : List GridPoint) (h : FamilyMember row F9B004L34) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L34, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R09280G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09280G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09280G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09280G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09280G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09280G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09280G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09280G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09280G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09280G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09280G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09280G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09280G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09280G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09280G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09280G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09280G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09280G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09280G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09280G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09280G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09280G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09280G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09280G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09280G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09280G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09280G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09280G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09280G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09280G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09280G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09280G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
