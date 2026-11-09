import Lean.Elab.Tactic.BuiltinTactic
import Lean.Meta.AppBuilder
import F10All
import F9B004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem C9R09024G0 (row : List GridPoint) (h : row ∈ [[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9024_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)] := by
    let c9r9024targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)]]
    let c9r9024choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9024targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2)] c9r9024choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9024targets, c9r9024choice, ?_, checked⟩
    intro S h
    simp only [c9r9024targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 27 _ (by rfl)
  have c9r9025_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)] := by
    let c9r9025targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,4),(1,3),(1,4),(2,1),(2,2),(2,3),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)]]
    let c9r9025choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9025targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1)] c9r9025choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9025targets, c9r9025choice, ?_, checked⟩
    intro S h
    simp only [c9r9025targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 30 _ (by rfl)
  have c9r9026_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)] := by
    let c9r9026targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,2)]]
    let c9r9026choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9026targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2)] c9r9026choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9026targets, c9r9026choice, ?_, checked⟩
    intro S h
    simp only [c9r9026targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 1 _ (by rfl)
  have c9r9027_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)] := by
    let c9r9027targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1),(6,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]]
    let c9r9027choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9027targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(4,1),(5,1)] c9r9027choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9027targets, c9r9027choice, ?_, checked⟩
    intro S h
    simp only [c9r9027targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 4 _ (by rfl)
  have c9r9028_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)] := by
    let c9r9028targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(4,4)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(3,5)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(3,5)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,4)]]
    let c9r9028choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 5) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9028targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4)] c9r9028choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9028targets, c9r9028choice, ?_, checked⟩
    intro S h
    simp only [c9r9028targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 8 _ (by rfl)
  have c9r9029_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)] := by
    let c9r9029targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)]]
    let c9r9029choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9029targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2)] c9r9029choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9029targets, c9r9029choice, ?_, checked⟩
    intro S h
    simp only [c9r9029targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 11 _ (by rfl)
  have c9r9030_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)] := by
    let c9r9030targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3),(5,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(3,4),(4,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(3,4),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3),(5,3)]]
    let c9r9030choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9030targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,3)] c9r9030choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9030targets, c9r9030choice, ?_, checked⟩
    intro S h
    simp only [c9r9030targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 13 _ (by rfl)
  have c9r9031_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)] := by
    let c9r9031targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,1),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)]]
    let c9r9031choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9031targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2)] c9r9031choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9031targets, c9r9031choice, ?_, checked⟩
    intro S h
    simp only [c9r9031targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 17 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9024_closed
  · subst row; exact c9r9025_closed
  · subst row; exact c9r9026_closed
  · subst row; exact c9r9027_closed
  · subst row; exact c9r9028_closed
  · subst row; exact c9r9029_closed
  · subst row; exact c9r9030_closed
  · subst row; exact c9r9031_closed
theorem C9R09024G1 (row : List GridPoint) (h : row ∈ [[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9032_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)] := by
    let c9r9032targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2),(5,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(4,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,3)]]
    let c9r9032choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 4) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9032targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3)] c9r9032choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9032targets, c9r9032choice, ?_, checked⟩
    intro S h
    simp only [c9r9032targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 20 _ (by rfl)
  have c9r9033_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)] := by
    let c9r9033targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2),(6,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(3,3),(4,3),(5,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(3,3),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,1),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(4,3),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(5,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2),(6,2)]]
    let c9r9033choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 1) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 3) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 2) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9033targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,2),(4,2),(5,2)] c9r9033choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9033targets, c9r9033choice, ?_, checked⟩
    intro S h
    simp only [c9r9033targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 23 _ (by rfl)
  have c9r9034_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)] := by
    let c9r9034targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,2),(2,4),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9034choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9034targets [(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3)] c9r9034choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9034targets, c9r9034choice, ?_, checked⟩
    intro S h
    simp only [c9r9034targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 29 _ (by rfl)
  have c9r9035_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r9035targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(2,1),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r9035choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9035targets [(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r9035choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9035targets, c9r9035choice, ?_, checked⟩
    intro S h
    simp only [c9r9035targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 2 _ (by rfl)
  have c9r9036_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r9036targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9036choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9036targets [(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r9036choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9036targets, c9r9036choice, ?_, checked⟩
    intro S h
    simp only [c9r9036targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 7 _ (by rfl)
  have c9r9037_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r9037targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,4),(1,3),(1,4),(2,1),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r9037choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,1)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9037targets [(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r9037choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9037targets, c9r9037choice, ?_, checked⟩
    intro S h
    simp only [c9r9037targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,false,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 10 _ (by rfl)
  have c9r9038_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r9038targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,4),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r9038choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9038targets [(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r9038choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9038targets, c9r9038choice, ?_, checked⟩
    intro S h
    simp only [c9r9038targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 12 _ (by rfl)
  have c9r9039_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r9039targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,3),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,4),(1,3),(1,4),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r9039choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (5,(0,0)) else (6,(0,1))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (9,(0,1)) else (10,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (13,(0,0)) else (14,(0,0))))))
    have checked : successorFastRowCheck c9r9039targets [(0,3),(1,2),(1,3),(2,0),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r9039choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9039targets, c9r9039choice, ?_, checked⟩
    intro S h
    simp only [c9r9039targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 14 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9032_closed
  · subst row; exact c9r9033_closed
  · subst row; exact c9r9034_closed
  · subst row; exact c9r9035_closed
  · subst row; exact c9r9036_closed
  · subst row; exact c9r9037_closed
  · subst row; exact c9r9038_closed
  · subst row; exact c9r9039_closed
theorem C9R09024G2 (row : List GridPoint) (h : row ∈ [[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9040_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r9040targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,0),(3,3),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,0),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(2,0),(2,1),(2,4),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(2,1),(2,4),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9040choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 2) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (1,(0,0))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 0) then (2,(0,0)) else (3,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (4,(0,0)) else (5,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 1) then (6,(0,1)) else (7,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (8,(0,0)) else (9,(0,0))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (10,(0,1)) else (11,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (14,(0,0)) else (15,(0,0))))))
    have checked : successorFastRowCheck c9r9040targets [(0,3),(1,2),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)] c9r9040choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9040targets, c9r9040choice, ?_, checked⟩
    intro S h
    simp only [c9r9040targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,false,true,true,false,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,false,true,true,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 21 _ (by rfl)
  have c9r9041_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] := by
    let c9r9041targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(3,4),(4,0),(4,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(2,4),(2,5),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,4)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)]]
    let c9r9041choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 5) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9041targets [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1)] c9r9041choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9041targets, c9r9041choice, ?_, checked⟩
    intro S h
    simp only [c9r9041targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 27 _ (by rfl)
  have c9r9042_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] := by
    let c9r9042targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2)],[(0,4),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)]]
    let c9r9042choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r9042targets [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2)] c9r9042choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9042targets, c9r9042choice, ?_, checked⟩
    intro S h
    simp only [c9r9042targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 0 _ (by rfl)
  have c9r9043_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] := by
    let c9r9043targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(3,3)],[(0,4),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(3,4)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,3)]]
    let c9r9043choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9043targets [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3)] c9r9043choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9043targets, c9r9043choice, ?_, checked⟩
    intro S h
    simp only [c9r9043targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 4 _ (by rfl)
  have c9r9044_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] := by
    let c9r9044targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,0)],[(0,4),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,0)],[(0,4),(1,3),(1,4),(2,2),(2,3),(2,4),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)]]
    let c9r9044choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (9,(0,0)) else (10,(0,1))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9044targets [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0)] c9r9044choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9044targets, c9r9044choice, ?_, checked⟩
    intro S h
    simp only [c9r9044targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 6 _ (by rfl)
  have c9r9045_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] := by
    let c9r9045targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,0),(3,1),(4,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(2,4),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)]]
    let c9r9045choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9045targets [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1)] c9r9045choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9045targets, c9r9045choice, ?_, checked⟩
    intro S h
    simp only [c9r9045targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 8 _ (by rfl)
  have c9r9046_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] := by
    let c9r9046targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(2,4),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,3),(4,0),(4,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(2,4),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1),(5,1)]]
    let c9r9046choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 4) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (10,(0,1)) else (11,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9046targets [(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(4,0),(4,1)] c9r9046choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9046targets, c9r9046choice, ?_, checked⟩
    intro S h
    simp only [c9r9046targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 27 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 13 _ (by rfl)
  have c9r9047_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] := by
    let c9r9047targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(3,4)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,3)]]
    let c9r9047choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 4) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9047targets [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3)] c9r9047choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9047targets, c9r9047choice, ?_, checked⟩
    intro S h
    simp only [c9r9047targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 20 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9040_closed
  · subst row; exact c9r9041_closed
  · subst row; exact c9r9042_closed
  · subst row; exact c9r9043_closed
  · subst row; exact c9r9044_closed
  · subst row; exact c9r9045_closed
  · subst row; exact c9r9046_closed
  · subst row; exact c9r9047_closed
theorem C9R09024G3 (row : List GridPoint) (h : row ∈ [[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)]]) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  have c9r9048_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] := by
    let c9r9048targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,0)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,0)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)]]
    let c9r9048choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9048targets [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0)] c9r9048choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9048targets, c9r9048choice, ?_, checked⟩
    intro S h
    simp only [c9r9048targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 23 _ (by rfl)
  have c9r9049_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] := by
    let c9r9049targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)]]
    let c9r9049choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,0)) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (10,(0,0)) else (11,(0,0))))))
    have checked : successorFastRowCheck c9r9049targets [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1)] c9r9049choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9049targets, c9r9049choice, ?_, checked⟩
    intro S h
    simp only [c9r9049targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 18 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 25 _ (by rfl)
  have c9r9050_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] := by
    let c9r9050targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(3,3),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2),(5,2)]]
    let c9r9050choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9050targets [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,2)] c9r9050choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9050targets, c9r9050choice, ?_, checked⟩
    intro S h
    simp only [c9r9050targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,false,true,true] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 11 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 19 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 26 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 27 _ (by rfl)
  have c9r9051_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] := by
    let c9r9051targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(4,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)]]
    let c9r9051choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9051targets [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1)] c9r9051choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9051targets, c9r9051choice, ?_, checked⟩
    intro S h
    simp only [c9r9051targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 12 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 0 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 20 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 30 _ (by rfl)
  have c9r9052_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] := by
    let c9r9052targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,0),(6,0)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,0),(5,0)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(5,0)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,0)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,1),(3,2),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0),(6,0)]]
    let c9r9052choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (8,(0,0)) else (9,(0,1)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < -1) then (10,(0,0)) else (11,(0,1))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 0) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9052targets [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(5,0)] c9r9052choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9052targets, c9r9052choice, ?_, checked⟩
    intro S h
    simp only [c9r9052targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 13 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,true] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 6 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 22 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 29 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 31 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 0 _ (by rfl)
  have c9r9053_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] := by
    let c9r9053targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(5,2)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(4,2)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(4,3)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,2)]]
    let c9r9053choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 3) then (9,(0,0)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9053targets [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2)] c9r9053choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9053targets, c9r9053choice, ?_, checked⟩
    intro S h
    simp only [c9r9053targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 14 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,true] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 7 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 28 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 1 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 3 _ (by rfl)
  have c9r9054_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] := by
    let c9r9054targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1),(5,1),(6,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,0),(3,1),(4,1),(5,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,0),(3,1),(3,2),(4,2),(5,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,0),(4,1),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(4,2),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,0),(5,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(5,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1),(6,1)]]
    let c9r9054choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < -1) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (4,(0,0))) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (5,(0,0)) else (6,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 2) then (7,(0,1)) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 0) then (8,(0,0)) else (9,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 2) then (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (10,(0,0)) else (11,(0,0))) else (if b.1 < 6 ∨ (b.1 = 6 ∧ b.2 < 1) then (12,(0,0)) else (13,(0,0))))))
    have checked : successorFastRowCheck c9r9054targets [(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(4,1),(5,1)] c9r9054choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9054targets, c9r9054choice, ?_, checked⟩
    intro S h
    simp only [c9r9054targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 15 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 3 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 25 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 30 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 2 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 5 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 6 _ (by rfl)
  have c9r9055_closed : FamilyRowClosed (fun S => FamilyMember S family10) [(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] := by
    let c9r9055targets : Array (List GridPoint) := #[[(0,3),(1,3),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2),(5,0),(5,1)],[(0,2),(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(0,4),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(1,4),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,0),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,0),(3,1),(3,2),(4,0),(4,1)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(3,3),(4,0),(4,1)],[(0,4),(1,3),(1,4),(2,2),(2,3),(3,2),(3,3),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(4,2)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,0)],[(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1),(5,1)]]
    let c9r9055choice (b : GridPoint) : ℕ × GridPoint := (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 3) then (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 1) then (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 2) then (0,(1,0)) else (if b.1 < 0 ∨ (b.1 = 0 ∧ b.2 < 4) then (1,(0,0)) else (2,(0,0)))) else (if b.1 < 1 ∨ (b.1 = 1 ∧ b.2 < 4) then (3,(0,0)) else (if b.1 < 2 ∨ (b.1 = 2 ∧ b.2 < 0) then (4,(0,0)) else (5,(0,0))))) else (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < -1) then (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 0) then (6,(0,0)) else (if b.1 < 3 ∨ (b.1 = 3 ∧ b.2 < 3) then (7,(0,0)) else (8,(0,0)))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 0) then (if b.1 < 4 ∨ (b.1 = 4 ∧ b.2 < 2) then (9,(0,1)) else (10,(0,0))) else (if b.1 < 5 ∨ (b.1 = 5 ∧ b.2 < 1) then (11,(0,0)) else (12,(0,0))))))
    have checked : successorFastRowCheck c9r9055targets [(0,3),(1,2),(1,3),(2,1),(2,2),(3,1),(3,2),(4,0),(4,1)] c9r9055choice = true := by
      run_tac do
        Lean.Elab.Tactic.withMainContext do
          let g ← Lean.Elab.Tactic.getMainGoal
          let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← g.getType))
          let pf ← Lean.Meta.mkDecideProof t
          g.assign pf
          Lean.Elab.Tactic.replaceMainGoal []
    refine ⟨c9r9055targets, c9r9055choice, ?_, checked⟩
    intro S h
    simp only [c9r9055targets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,false,false,false,true,true,false,false] 4 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,false,true,false,true,false,false,true,true,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,false,true,true,false,false,true,true,false] 17 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,false,true,true,false,false,true] 16 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,false,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,false,false,true] 23 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,false] 21 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 8 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,true,true,false,false,true,false,true,false] 24 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 9 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 10 _ (by rfl)
    · subst S
      exact familyLookup_sound family10 [true,true,true,false,true,false,true,true,false,true] 11 _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst row; exact c9r9048_closed
  · subst row; exact c9r9049_closed
  · subst row; exact c9r9050_closed
  · subst row; exact c9r9051_closed
  · subst row; exact c9r9052_closed
  · subst row; exact c9r9053_closed
  · subst row; exact c9r9054_closed
  · subst row; exact c9r9055_closed
theorem C9R09024_closed (row : List GridPoint) (h : FamilyMember row F9B004L26) : FamilyRowClosed (fun S => FamilyMember S family10) row := by
  simp only [F9B004L26, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst row; exact C9R09024G0 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09024G0 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09024G0 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09024G0 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09024G0 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09024G0 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09024G0 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09024G0 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09024G1 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09024G1 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09024G1 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09024G1 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09024G1 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09024G1 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09024G1 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09024G1 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09024G2 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09024G2 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09024G2 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09024G2 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09024G2 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09024G2 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09024G2 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09024G2 _ (List.mem_of_getElem? (i := 7) (by rfl))
  · subst row; exact C9R09024G3 _ (List.mem_of_getElem? (i := 0) (by rfl))
  · subst row; exact C9R09024G3 _ (List.mem_of_getElem? (i := 1) (by rfl))
  · subst row; exact C9R09024G3 _ (List.mem_of_getElem? (i := 2) (by rfl))
  · subst row; exact C9R09024G3 _ (List.mem_of_getElem? (i := 3) (by rfl))
  · subst row; exact C9R09024G3 _ (List.mem_of_getElem? (i := 4) (by rfl))
  · subst row; exact C9R09024G3 _ (List.mem_of_getElem? (i := 5) (by rfl))
  · subst row; exact C9R09024G3 _ (List.mem_of_getElem? (i := 6) (by rfl))
  · subst row; exact C9R09024G3 _ (List.mem_of_getElem? (i := 7) (by rfl))
end Polyomino57
